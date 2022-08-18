/*-------------------------------------------------------------------------
 *
 * polar_logindex.c
 *   Implementation of parse xlog states and replay.
 *
 * Copyright (c) 2020, Alibaba Group Holding Limited
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 * http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 *
 * IDENTIFICATION
 *    src/backend/access/logindex/polar_logindex.c
 *
 *-------------------------------------------------------------------------
 */
#include "postgres.h"

#include <sys/stat.h>
#include <unistd.h>

#include "access/hash.h"
#include "access/polar_logindex.h"
#include "access/polar_logindex_internal.h"
#include "access/slru.h"
#include "access/transam.h"
#include "access/xlogdefs.h"
#include "miscadmin.h"
#include "port/atomics.h"
#include "port/pg_crc32c.h"
#include "postmaster/startup.h"
#include "utils/hashutils.h"
#include "utils/memutils.h"

static log_index_io_err_t       logindex_io_err = 0;
static int                      logindex_errno = 0;

static void log_index_insert_new_item(log_index_lsn_t *lsn_info, log_mem_table_t *table, uint32 key, log_seg_id_t new_item_id);
static void log_index_insert_new_seg(log_mem_table_t *table, log_seg_id_t head, log_seg_id_t seg_id, log_index_lsn_t *lsn_info);

// Xi: check whether snapshot has this state
// States includes: POLAR_LOGINDEX_STATE_INITIALIZED,
//                  POLAR_LOGINDEX_STATE_ADDING,
//                  POLAR_LOGINDEX_STATE_WRITABLE
bool
polar_logindex_check_state(log_index_snapshot_t *logindex_snapshot, uint32 state)
{
	return pg_atomic_read_u32(&logindex_snapshot->state) & state;
}

// Xi: If Context exists, return it. Otherwise, create and return it.
MemoryContext
polar_logindex_memory_context(void)
{
	static MemoryContext context = NULL;

	if (context == NULL)
	{
		context = AllocSetContextCreate(TopMemoryContext,
										"logindex snapshot mem context",
										ALLOCSET_DEFAULT_SIZES);
		MemoryContextAllowInCriticalSection(context, true);
	}

	return context;
}

XLogRecPtr
log_index_item_max_lsn(log_idx_table_data_t *table, log_item_head_t *item)
{
	log_item_seg_t *seg;

    //XI: if there is only head node, get the last record in suffix_lsn[] list
	if (item->head_seg == item->tail_seg)
		return LOG_INDEX_SEG_MAX_LSN(table, item);

    // XI: search the list tail item, that item has the max LSN
	seg = log_index_item_seg(table, item->tail_seg);
	Assert(seg != NULL);

	return LOG_INDEX_SEG_MAX_LSN(table, seg);
}

// XI: One snapShot has many logIndexMemTables
static Size
log_index_mem_tbl_shmem_size(uint64 logindex_mem_tbl_size)
{
	Size size = offsetof(log_index_snapshot_t, mem_table);
	size = add_size(size, mul_size(sizeof(log_mem_table_t), logindex_mem_tbl_size));

	size = MAXALIGN(size);

	/* The number of logindex memory table is at least 3 */
	if (logindex_mem_tbl_size < 3)
		elog(FATAL, "The number=%ld of logindex memory table is less than 3", logindex_mem_tbl_size);
	else
		ereport(LOG, (errmsg("The total log index memory table size is %ld", size)));

	return size;
}


static Size
log_index_bloom_shmem_size(int bloom_blocks)
{
	Size  size = SimpleLruShmemSize(bloom_blocks, 0);

	return MAXALIGN(size);
}

static Size
log_index_lwlock_shmem_size(uint64 logindex_mem_tbl_size)
{
	Size size = mul_size(sizeof(LWLockMinimallyPadded), LOG_INDEX_LWLOCK_NUM(logindex_mem_tbl_size));

	return MAXALIGN(size);
}

Size
polar_logindex_shmem_size(uint64 logindex_mem_tbl_size, int bloom_blocks)
{
	Size size = 0;

	size = add_size(size, log_index_mem_tbl_shmem_size(logindex_mem_tbl_size));

	size = add_size(size, log_index_bloom_shmem_size(bloom_blocks));

	size = add_size(size, log_index_lwlock_shmem_size(logindex_mem_tbl_size));

	return CACHELINEALIGN(size);
}

//XI: What is "promote", maybe it means the process that primary node write LogIndex to disk
//XI: This function reflect whether this table has been saved
//XI: Get promoted_info from snapshot. If promoted_info shows $table->tid has been saved, return true
static bool
log_index_table_saved_before_promote(log_index_snapshot_t *logindex_snapshot, log_mem_table_t *table)
{
	log_index_promoted_info_t *promoted_info = &logindex_snapshot->promoted_info;
	bool saved = false;

	if (unlikely(promoted_info->old_rw_saved_max_tid != LOG_INDEX_TABLE_INVALID_ID))
	{
		saved = LOG_INDEX_MEM_TBL_TID(table) <= promoted_info->old_rw_saved_max_tid;

		if (LOG_INDEX_MEM_TBL_TID(table) == promoted_info->old_rw_saved_max_tid)
		{
			if (table->data.max_lsn != promoted_info->old_rw_saved_max_lsn)
				elog(PANIC, "promote last table max_lsn=%lX, max lsn saved by old rw is %lX",
					 table->data.max_lsn, promoted_info->old_rw_saved_max_lsn);
		}

	}

	return saved;
}

static bool
log_index_flush_table(log_index_snapshot_t *logindex_snapshot, XLogRecPtr checkpoint_lsn, bool flush_active)
{
	log_mem_table_t *table;
	LWLock *lock;
	log_index_meta_t *meta = &logindex_snapshot->meta;
	uint32 mid;
	bool need_flush;
	bool succeed = true;
	int  flushed = 0;
	bool write_done = false;
	static XLogRecPtr last_flush_max_lsn = InvalidXLogRecPtr;

	SpinLockAcquire(LOG_INDEX_SNAPSHOT_LOCK);
	mid = meta->max_idx_table_id % logindex_snapshot->mem_tbl_size;
	SpinLockRelease(LOG_INDEX_SNAPSHOT_LOCK);

	do
	{
		log_idx_table_id_t tid = LOG_INDEX_TABLE_INVALID_ID;
		XLogRecPtr table_min_lsn, table_max_lsn;

		table = LOG_INDEX_MEM_TBL(mid);

		if (LOG_INDEX_MEM_TBL_STATE(table) == LOG_INDEX_MEM_TBL_STATE_INACTIVE ||
				(flush_active &&
				 LOG_INDEX_MEM_TBL_STATE(table) == LOG_INDEX_MEM_TBL_STATE_ACTIVE &&
				 !LOG_INDEX_MEM_TBL_IS_NEW(table)))
		{
			lock = LOG_INDEX_MEM_TBL_LOCK(table);
			LWLockAcquire(lock, LW_EXCLUSIVE);

			/* Nothing to change since last flush table */
			if (flush_active &&
					LOG_INDEX_MEM_TBL_STATE(table) == LOG_INDEX_MEM_TBL_STATE_ACTIVE &&
					last_flush_max_lsn == table->data.max_lsn &&
					!LOG_INDEX_MEM_TBL_IS_NEW(table))
			{
				LWLockRelease(lock);
				write_done = true;
				break;
			}

			/*
			 * Check state again, it may be force flushed by other process.
			 * During crash recovery GetFlushRecPtr return invalid value, so we compare
			 * with GetXLogReplayRecPtr().
			 */
			if ((LOG_INDEX_MEM_TBL_STATE(table) == LOG_INDEX_MEM_TBL_STATE_INACTIVE ||
					LOG_INDEX_MEM_TBL_STATE(table) == LOG_INDEX_MEM_TBL_STATE_ACTIVE)
					&& logindex_snapshot->table_flushable(table, logindex_snapshot->extra_data))
			{
				/*
				 * After promoting don't write table which was flushed by previous rw node
				 */
				if (log_index_table_saved_before_promote(logindex_snapshot, table))
					succeed = true;
				else
					succeed = log_index_write_table(logindex_snapshot, table);

				if (succeed)
				{
					/* Only inactive table can set FLUSHED */
					if (LOG_INDEX_MEM_TBL_STATE(table) == LOG_INDEX_MEM_TBL_STATE_INACTIVE)
						LOG_INDEX_MEM_TBL_SET_STATE(table, LOG_INDEX_MEM_TBL_STATE_FLUSHED);

					/* save last flush fullpage logindex max_lsn for active table */
					if (flush_active)
						last_flush_max_lsn = table->data.max_lsn;

					flushed++;
					tid = LOG_INDEX_MEM_TBL_TID(table);
					table_max_lsn = table->data.max_lsn;
					table_min_lsn = table->data.min_lsn;

					ereport(polar_trace_logindex(DEBUG4), (errmsg("flush logindex tid=%ld,min_lsn=%lX,max_lsn=%lX", tid, table_min_lsn, table_max_lsn),
														   errhidestmt(true),
														   errhidecontext(true)));
				}
			}

			LWLockRelease(lock);
		}

		/*
		 * If checkpoint lsn is valid we will flush all table which state is INACTIVE
		 * and table's lsn is smaller than checkpoint lsn.
		 * If consistent lsn is larger than max saved logindex lsn, we will try to flush table until saved logindex lsn
		 * is larger than consistent lsn.
		 * Otherwise we will try to flush all INACTIVE table, but don't flush table number more
		 * than polar_logindex_table_batch_size.
		 */
		SpinLockAcquire(LOG_INDEX_SNAPSHOT_LOCK);
		table = LOG_INDEX_MEM_TBL_ACTIVE();

		need_flush = LOG_INDEX_MEM_TBL_TID(table) > (meta->max_idx_table_id + 1);

		if (need_flush)
		{
			if (XLogRecPtrIsInvalid(checkpoint_lsn))
			{
				need_flush = flushed < polar_logindex_table_batch_size;
			}
			else
			{
				need_flush = (checkpoint_lsn > meta->max_lsn
							  && !(checkpoint_lsn >= table->data.min_lsn && checkpoint_lsn <= table->data.max_lsn));
			}
		}
		else
			write_done = true;

		mid = meta->max_idx_table_id;
		SpinLockRelease(LOG_INDEX_SNAPSHOT_LOCK);

		mid %= logindex_snapshot->mem_tbl_size;
	}
	while (need_flush);

	return write_done;
}

static bool
log_index_rw_bg_write(log_index_snapshot_t *logindex_snapshot)
{
	return log_index_flush_table(logindex_snapshot, InvalidXLogRecPtr, false);
}

void
polar_logindex_flush_table(logindex_snapshot_t logindex_snapshot, XLogRecPtr checkpoint_lsn)
{
	log_index_flush_table(logindex_snapshot, checkpoint_lsn, false);
}

void
polar_logindex_flush_active_table(log_index_snapshot_t *logindex_snapshot)
{
	log_index_flush_table(logindex_snapshot, InvalidXLogRecPtr, true);
}

void
polar_logindex_invalid_bloom_cache(log_index_snapshot_t *logindex_snapshot, log_idx_table_id_t tid)
{
	int pageno = LOG_INDEX_TBL_BLOOM_PAGE_NO(tid);

	polar_slru_invalid_page(&logindex_snapshot->bloom_ctl, pageno);
}

static void
polar_logindex_local_cache_seg2str(char *seg_str, uint64 segno)
{
	LOG_INDEX_LOCAL_CACHE_SEG_NAME(seg_str, segno);
}

static bool
polar_logindex_local_cache_scan_callback(polar_local_cache cache, char *cache_file, uint64 segno)
{
	uint64  cur_segno = 0;
	char suffix[5] = {0};
	polar_cache_io_error io_error;

	if (sscanf(cache_file, "%016lX%4s", &cur_segno, suffix) == 2 && strcmp(suffix, ".tbl") == 0)
	{
		if (cur_segno > 0 && cur_segno < segno)
		{
			if (!polar_local_cache_remove(cache, cur_segno, &io_error))
				polar_local_cache_report_error(cache, &io_error, LOG);
		}
	}

	return true;
}


static void
polar_logindex_truncate_local_cache(logindex_snapshot_t logindex_snapshot, uint64 segno)
{
	static uint64_t last_min_segno = 0;

	if (segno != 0 && logindex_snapshot->segment_cache)
	{
		if (last_min_segno < segno)
		{
			polar_local_cache_scan(
				logindex_snapshot->segment_cache,
				polar_logindex_local_cache_scan_callback,
				segno);
			last_min_segno = segno;
		}
	}
}

static void
log_index_update_ro_table_state(log_index_snapshot_t *logindex_snapshot, log_idx_table_id_t max_saved_tid)
{
	uint32 mid;
	log_mem_table_t *table;
	LWLock *lock;
	bool need_flush = false;

	if (max_saved_tid == LOG_INDEX_TABLE_INVALID_ID)
		return;

	mid = (max_saved_tid - 1) % logindex_snapshot->mem_tbl_size;

	/* Update table state from maximum saved table to maximum table in memory */
	do
	{
		table = LOG_INDEX_MEM_TBL(mid);
		lock = LOG_INDEX_MEM_TBL_LOCK(table);

		need_flush = LOG_INDEX_MEM_TBL_STATE(table) == LOG_INDEX_MEM_TBL_STATE_INACTIVE;

		if (need_flush)
		{
			LWLockAcquire(lock, LW_EXCLUSIVE);

			/* Check state again, it may be force flushed by other process */
			if (LOG_INDEX_MEM_TBL_STATE(table) == LOG_INDEX_MEM_TBL_STATE_INACTIVE
					&& LOG_INDEX_MEM_TBL_TID(table) <= max_saved_tid)
			{
				polar_logindex_invalid_bloom_cache(logindex_snapshot, LOG_INDEX_MEM_TBL_TID(table));
				LOG_INDEX_MEM_TBL_SET_STATE(table, LOG_INDEX_MEM_TBL_STATE_FLUSHED);
			}

			LWLockRelease(lock);
		}

		mid = LOG_INDEX_MEM_TBL_PREV_ID(mid);
	}
	while (need_flush);
}

static bool
log_index_ro_bg_write(log_index_snapshot_t *logindex_snapshot)
{
	log_index_meta_t *meta = &logindex_snapshot->meta;
	log_idx_table_id_t max_tid, max_saved_tid = LOG_INDEX_TABLE_INVALID_ID;
	static log_idx_table_id_t last_max_table_id = 0;
	uint64 fresh_min_segno = 0;

	SpinLockAcquire(LOG_INDEX_SNAPSHOT_LOCK);
	max_tid = logindex_snapshot->max_idx_table_id;
	SpinLockRelease(LOG_INDEX_SNAPSHOT_LOCK);

	if (max_tid == last_max_table_id)
	{
		/* Return true if no new table is added and no table state need to be updated */
		return true;
	}

	last_max_table_id = max_tid;

	LWLockAcquire(LOG_INDEX_IO_LOCK, LW_EXCLUSIVE);

	if (log_index_get_meta(logindex_snapshot, meta))
	{
		max_saved_tid = meta->max_idx_table_id;
		fresh_min_segno = meta->min_segment_info.segment_no;
	}
	else
		elog(WARNING, "Failed to get logindex meta from storage");

	LWLockRelease(LOG_INDEX_IO_LOCK);

	log_index_update_ro_table_state(logindex_snapshot, max_saved_tid);
	polar_logindex_truncate_local_cache(logindex_snapshot, fresh_min_segno);

	/* Return true because we updated all table state which we can update */
	return true;
}

bool
polar_logindex_bg_write(logindex_snapshot_t logindex_snapshot)
{
	bool write_done = true;

	if (likely(polar_logindex_check_state(logindex_snapshot, POLAR_LOGINDEX_STATE_ADDING)))
	{
		if (!polar_logindex_check_state(logindex_snapshot, POLAR_LOGINDEX_STATE_WRITABLE))
			write_done &= log_index_ro_bg_write(logindex_snapshot);
		else
			write_done &= log_index_rw_bg_write(logindex_snapshot);
	}

	return write_done;
}

static void
log_index_init_lwlock(log_index_snapshot_t *logindex_snapshot, int offset, int size, int tranche_id, const char *name)
{
	int i, j;

	LWLockRegisterTranche(tranche_id, name);

	for (i = offset, j = 0; j < size; i++, j++)
		LWLockInitialize(&(logindex_snapshot->lwlock_array[i].lock), tranche_id);
}

static void
polar_logindex_snapshot_remove_data(logindex_snapshot_t logindex_snapshot)
{
	char path[MAXPGPATH] = {0};

	/* We cannot remove logindex files if it's not writable */
	if (!polar_logindex_check_state(logindex_snapshot, POLAR_LOGINDEX_STATE_WRITABLE))
		return;

	if (strlen(logindex_snapshot->dir) > 0)
	{
		POLAR_FILE_PATH(path, logindex_snapshot->dir);
		rmtree(path, false);
	}
}

static void
logindex_snapshot_init_promoted_info(log_index_snapshot_t *logindex_snapshot)
{
	log_index_promoted_info_t *info = &logindex_snapshot->promoted_info;

	info->old_rw_saved_max_lsn = InvalidXLogRecPtr;
	info->old_rw_max_inserted_lsn = InvalidXLogRecPtr;
	info->old_rw_max_tid = LOG_INDEX_TABLE_INVALID_ID;
	info->old_rw_saved_max_tid = LOG_INDEX_TABLE_INVALID_ID;
}

static XLogRecPtr
polar_logindex_snapshot_base_init(log_index_snapshot_t *logindex_snapshot, XLogRecPtr checkpoint_lsn)
{
	log_index_meta_t *meta = &logindex_snapshot->meta;
	XLogRecPtr start_lsn = checkpoint_lsn;

	Assert(!polar_logindex_check_state(logindex_snapshot, POLAR_LOGINDEX_STATE_INITIALIZED));
	Assert(!XLogRecPtrIsInvalid(checkpoint_lsn));

	LWLockAcquire(LOG_INDEX_IO_LOCK, LW_EXCLUSIVE);

	/*
	 * Reset logindex when we can not get correct logindex meta from storage
	 */
	if (!log_index_get_meta(logindex_snapshot, meta))
	{
		polar_logindex_snapshot_remove_data(logindex_snapshot);
		MemSet(meta, 0, sizeof(log_index_meta_t));
	}

	POLAR_LOG_LOGINDEX_META_INFO(meta);

    //XI: there are max_idx_table_id tables created, and the tables will be set inactive in mem_tbl_size size
	logindex_snapshot_init_promoted_info(logindex_snapshot);
	logindex_snapshot->max_idx_table_id = meta->max_idx_table_id;
	LOG_INDEX_MEM_TBL_ACTIVE_ID = meta->max_idx_table_id % logindex_snapshot->mem_tbl_size;

	logindex_snapshot->max_lsn = meta->max_lsn;
	MemSet(logindex_snapshot->mem_table, 0,
		   sizeof(log_mem_table_t) * logindex_snapshot->mem_tbl_size);

	/*
	 * If meta->start_lsn is invalid, we will not parse xlog and save it to logindex.
	 * RO will check logindex meta again when parse checkpoint xlog.
	 * RW will set logindex meta start lsn and save to storage when create new checkpoint.
	 * This will make ro and rw to create logindex from the same checkpoint.
	 */

	if (!XLogRecPtrIsInvalid(meta->start_lsn)
			&& meta->start_lsn < checkpoint_lsn)
		start_lsn = meta->start_lsn;

	/*
	 * When we start to truncate lsn , latest_page_number may not be set up; insert a
	 * suitable value to bypass the sanity test in SimpleLruTruncate.
	 */
	logindex_snapshot->bloom_ctl.shared->latest_page_number = UINT32_MAX;

	LWLockRelease(LOG_INDEX_IO_LOCK);

	/*
	 * When initialize log index snapshot, we load max table id's data to memory.
	 * When first insert lsn to memory table, need to check whether it already exists
	 * in previous table
	 */
	polar_load_logindex_snapshot_from_storage(logindex_snapshot, checkpoint_lsn);

	pg_atomic_fetch_or_u32(&logindex_snapshot->state, POLAR_LOGINDEX_STATE_INITIALIZED);

	return start_lsn;
}

XLogRecPtr
polar_logindex_snapshot_init(logindex_snapshot_t logindex_snapshot, XLogRecPtr checkpoint_lsn, bool read_only)
{
	XLogRecPtr start_lsn = InvalidXLogRecPtr;

	if (!read_only)
	{
		char dir[MAXPGPATH];
		snprintf(dir, MAXPGPATH, "%s/%s", POLAR_DATA_DIR(), logindex_snapshot->dir);
		polar_validate_dir(dir);

		pg_atomic_fetch_or_u32(&logindex_snapshot->state, POLAR_LOGINDEX_STATE_WRITABLE);
	}

	start_lsn = polar_logindex_snapshot_base_init(logindex_snapshot, checkpoint_lsn);

	ereport(LOG, (errmsg("Init %s succeed", logindex_snapshot->dir)));

	return start_lsn;
}


static void
log_index_init_lwlock_array(log_index_snapshot_t *logindex_snapshot, const char *name, int tranche_id_begin, int tranche_id_end)
{
	int i = 0;
	int tranche_id = tranche_id_begin;

	Assert(logindex_snapshot->mem_tbl_size > 0);
	/*
	 * The tranche id defined for logindex must map the following call sequence.
	 * See the definition of LWTRANCE_WAL_LOGINDEX_BEGIN and LWTRANCHE_WAL_LOGINDEX_END as example
	 */
	snprintf(logindex_snapshot->trache_name[i], NAMEDATALEN, " %s_mem", name);
	log_index_init_lwlock(logindex_snapshot, LOG_INDEX_MEMTBL_LOCK_OFFSET, logindex_snapshot->mem_tbl_size,
						  tranche_id++, logindex_snapshot->trache_name[i]);

	snprintf(logindex_snapshot->trache_name[++i], NAMEDATALEN, " %s_hash", name);
	log_index_init_lwlock(logindex_snapshot, LOG_INDEX_HASH_LOCK_OFFSET, LOG_INDEX_MEM_TBL_HASH_LOCK_NUM,
						  tranche_id++, logindex_snapshot->trache_name[i]);

	snprintf(logindex_snapshot->trache_name[++i], NAMEDATALEN, " %s_io", name);
	log_index_init_lwlock(logindex_snapshot, LOG_INDEX_IO_LOCK_OFFSET, 1,
						  tranche_id++, logindex_snapshot->trache_name[i]);

	snprintf(logindex_snapshot->trache_name[++i], NAMEDATALEN, " %s_bloom", name);
	log_index_init_lwlock(logindex_snapshot, LOG_INDEX_BLOOM_LRU_LOCK_OFFSET, 1,
						  tranche_id, logindex_snapshot->trache_name[i]);

	Assert(tranche_id == tranche_id_end);
	Assert((i + 1) == LOG_INDEX_MAX_TRACHE);
}

static bool
log_index_page_precedes(int page1, int page2)
{
	return page1 < page2;
}

logindex_snapshot_t
polar_logindex_snapshot_shmem_init(const char *name, uint64 logindex_mem_tbl_size, int bloom_blocks, int tranche_id_begin, int tranche_id_end,
								   logindex_table_flushable table_flushable, void *extra_data)
{
#define LOGINDEX_SNAPSHOT_SUFFIX "_snapshot"
#define LOGINDEX_LOCK_SUFFIX "_lock"
#define LOGINDEX_BLOOM_SUFFIX "_bloom"

	logindex_snapshot_t logindex_snapshot = NULL;
	bool        found_snapshot;
	bool        found_locks;
	Size        size;
	char        item_name[POLAR_MAX_SHMEM_NAME];

	size = log_index_mem_tbl_shmem_size(logindex_mem_tbl_size);

	StaticAssertStmt(sizeof(log_item_head_t) == LOG_INDEX_TBL_SEG_SIZE,
					 "log_item_head_t size is not same as LOG_INDEX_MEM_TBL_SEG_SIZE");
	StaticAssertStmt(sizeof(log_item_seg_t) == LOG_INDEX_TBL_SEG_SIZE,
					 "log_item_seg_t size is not same as LOG_INDEX_MEM_TBL_SEG_SIZE");

	StaticAssertStmt(LOG_INDEX_FILE_TBL_BLOOM_SIZE > sizeof(log_file_table_bloom_t),
					 "LOG_INDEX_FILE_TBL_BLOOM_SIZE is not enough for log_file_table_bloom_t");

	snprintf(item_name, POLAR_MAX_SHMEM_NAME, "%s%s", name, LOGINDEX_SNAPSHOT_SUFFIX);

	logindex_snapshot = (logindex_snapshot_t)
						ShmemInitStruct(item_name, size, &found_snapshot);
	Assert(logindex_snapshot != NULL);

	snprintf(item_name, POLAR_MAX_SHMEM_NAME, "%s%s", name, LOGINDEX_LOCK_SUFFIX);

	/* Align lwlocks to cacheline boundary */
	logindex_snapshot->lwlock_array = (LWLockMinimallyPadded *)
									  ShmemInitStruct(item_name, log_index_lwlock_shmem_size(logindex_mem_tbl_size),
													  &found_locks);

	if (!IsUnderPostmaster)
	{
		Assert(!found_snapshot && !found_locks);
		logindex_snapshot->mem_tbl_size = logindex_mem_tbl_size;

		pg_atomic_init_u32(&logindex_snapshot->state, 0);

		log_index_init_lwlock_array(logindex_snapshot, name, tranche_id_begin, tranche_id_end);

		logindex_snapshot->max_allocated_seg_no = 0;
		logindex_snapshot->table_flushable = table_flushable;
		logindex_snapshot->extra_data = extra_data;

		SpinLockInit(LOG_INDEX_SNAPSHOT_LOCK);

		StrNCpy(logindex_snapshot->dir, name, NAMEDATALEN);
		logindex_snapshot->segment_cache = NULL;
	}
	else
		Assert(found_snapshot && found_locks);

	logindex_snapshot->bloom_ctl.PagePrecedes = log_index_page_precedes;
	snprintf(item_name, POLAR_MAX_SHMEM_NAME, " %s%s", name, LOGINDEX_BLOOM_SUFFIX);

	/*
	 * Notice: When define tranche id for logindex, the last one is used for logindex bloom.
	 * See the definition between LWTRANCE_WAL_LOGINDEX_BEGIN and LWTRANCE_WAL_LOGINDEX_END
	 */
	SimpleLruInit(&logindex_snapshot->bloom_ctl, item_name,
				  bloom_blocks, 0,
				  LOG_INDEX_BLOOM_LRU_LOCK, name,
				  tranche_id_end, true);
	return logindex_snapshot;
}

static bool
log_index_handle_update_v1_to_v2(log_index_meta_t *meta)
{
	if (polar_is_standby())
		return false;

	return true;
}

static bool
log_index_data_compatible(log_index_meta_t *meta)
{
	switch (meta->version)
	{
		case 1:
			return log_index_handle_update_v1_to_v2(meta);

		case LOG_INDEX_VERSION:
			return true;

		default:
			return false;
	}
}

//XI: Read meta file("log_index_meta") from disk and validate data
bool
log_index_get_meta(log_index_snapshot_t *logindex_snapshot, log_index_meta_t *meta)
{
	int         r;
	char        meta_path[MAXPGPATH];
	pg_crc32    crc;
	int fd;

	MemSet(meta, 0, sizeof(log_index_meta_t));

	snprintf(meta_path, MAXPGPATH, "%s/%s/%s", POLAR_DATA_DIR(), logindex_snapshot->dir, LOG_INDEX_META_FILE);

	if ((fd = PathNameOpenFile(meta_path, O_RDONLY | PG_BINARY, true)) < 0)
		return false;


	r = polar_file_pread(fd, (char *)meta, sizeof(log_index_meta_t), 0, WAIT_EVENT_LOGINDEX_META_READ);
	logindex_errno = errno;

	FileClose(fd);

	if (r != sizeof(log_index_meta_t))
	{
		ereport(WARNING,
				(errmsg("could not read file \"%s\": read %d of %d and errno=%d",
						meta_path, r, (int) sizeof(log_index_meta_t), logindex_errno)));

		return false;
	}

	crc = meta->crc;

	if (meta->magic != LOG_INDEX_MAGIC)
	{
		POLAR_LOG_LOGINDEX_META_INFO(meta);
		ereport(WARNING,
				(errmsg("The magic number of meta file is incorrect, got %d, expect %d",
						meta->magic, LOG_INDEX_MAGIC)));

		return false;
	}

	meta->crc = 0;
	meta->crc = log_index_calc_crc((unsigned char *)meta, sizeof(log_index_meta_t));

	if (crc != meta->crc)
	{
		POLAR_LOG_LOGINDEX_META_INFO(meta);
		ereport(WARNING,
				(errmsg("The crc of file %s is incorrect, got %d but expect %d", meta_path,
						crc, meta->crc)));

		return false;
	}

	if (meta->version != LOG_INDEX_VERSION
			&& !log_index_data_compatible(meta))
	{
		POLAR_LOG_LOGINDEX_META_INFO(meta);
		ereport(WARNING,
				(errmsg("The version is incorrect and incompatible, got %d, expect %d",
						meta->version, LOG_INDEX_VERSION)));

		return false;
	}

	return true;
}

//XI: Return meta.start_lsn
XLogRecPtr
polar_logindex_start_lsn(logindex_snapshot_t logindex_snapshot)
{
	XLogRecPtr start_lsn = InvalidXLogRecPtr;

	if (logindex_snapshot != NULL)
	{
		LWLockAcquire(LOG_INDEX_IO_LOCK, LW_SHARED);
		start_lsn = logindex_snapshot->meta.start_lsn;
		LWLockRelease(LOG_INDEX_IO_LOCK);
	}

	return start_lsn;
}

// XI: Write and Sync meta to disk
// snapshot only provides with meta_path directory
void
polar_log_index_write_meta(log_index_snapshot_t *logindex_snapshot, log_index_meta_t *meta, bool update)
{
	File         fd;
	char         meta_path[MAXPGPATH];
	int          flag = O_RDWR | PG_BINARY;
	int          save_errno;

	snprintf(meta_path, MAXPGPATH, "%s/%s/%s", POLAR_DATA_DIR(), logindex_snapshot->dir, LOG_INDEX_META_FILE);

	if (meta->max_lsn != InvalidXLogRecPtr)
		meta->start_lsn = meta->max_lsn;

	meta->magic = LOG_INDEX_MAGIC;
	meta->version = LOG_INDEX_VERSION;
	meta->crc = 0;
	meta->crc = log_index_calc_crc((unsigned char *)meta, sizeof(log_index_meta_t));

	if (!update)
		flag |= O_CREAT;

	if ((fd = PathNameOpenFile(meta_path, flag, true)) == -1)
	{
		save_errno = errno;
		POLAR_LOG_LOGINDEX_META_INFO(meta);
		ereport(PANIC, (errmsg("could not open file \"%s\": \"%s\"", meta_path, strerror(save_errno))));
	}

	if (FileWrite(fd, (char *)meta, sizeof(log_index_meta_t), WAIT_EVENT_LOGINDEX_META_WRITE)
			!= sizeof(log_index_meta_t))
	{
		/* if write didn't set errno, assume problem is no disk space */
		if (errno == 0)
			errno = ENOSPC;

		save_errno = errno;
		POLAR_LOG_LOGINDEX_META_INFO(meta);
		ereport(PANIC, (errmsg("could not write file \"%s\": \"%s\"", meta_path, strerror(save_errno))));
	}

	if (FileSync(fd, WAIT_EVENT_LOGINDEX_META_FLUSH) != 0)
	{
		save_errno = errno;
		POLAR_LOG_LOGINDEX_META_INFO(meta);
		ereport(PANIC, (errmsg("could not flush file \"%s\": \"%s\"", meta_path, strerror(save_errno))));
	}

	FileClose(fd);
}

/*
 * Save table if it's running in master node's recovery process.
 * During master recovery, bgwriter is not started and we have to
 * synchronized save table to get active table.
 */
//XI: If this snapshot is not WRITABLE, check meta whether this table has been saved,
//      if so, invalidate this table's bloom data and set table as FLUSHED
//    If this snapshot is WRITABLE and this table is flushable, check promoted_info,
//      if this table has been save to shared disk, do nothing, just set state as FLUSHED,
//      else, write table data and bloom data to disk
void
log_index_force_save_table(log_index_snapshot_t *logindex_snapshot, log_mem_table_t *table)
{
	static log_idx_table_id_t force_table = LOG_INDEX_TABLE_INVALID_ID;
	log_index_meta_t *meta = &logindex_snapshot->meta;
	log_idx_table_id_t tid = LOG_INDEX_MEM_TBL_TID(table);

	if (force_table != tid)
	{
		elog(LOG, "force save table %ld", tid);
		force_table = tid;
	}

	if (!polar_logindex_check_state(logindex_snapshot, POLAR_LOGINDEX_STATE_WRITABLE))
	{
		log_idx_table_id_t max_tid;

		LWLockAcquire(LOG_INDEX_IO_LOCK, LW_EXCLUSIVE);

        //XI: get the max_tid that have been saved
		if (log_index_get_meta(logindex_snapshot, meta))
			max_tid = meta->max_idx_table_id;
		else
			elog(FATAL, "Failed to get logindex meta from storage");

		LWLockRelease(LOG_INDEX_IO_LOCK);

        //XI: if meta shows this table has been saved, invalidate this table's bloom data, and set
        //      this table state as FLUSHED
		if (max_tid >= LOG_INDEX_MEM_TBL_TID(table))
		{
			polar_logindex_invalid_bloom_cache(logindex_snapshot, LOG_INDEX_MEM_TBL_TID(table));
			LOG_INDEX_MEM_TBL_SET_STATE(table, LOG_INDEX_MEM_TBL_STATE_FLUSHED);
		}
	}
	else
	{
		if (logindex_snapshot->table_flushable(table, logindex_snapshot->extra_data))
		{
			bool succeed = false;

            //XI: if this table has already been save, just ignore it and set state as FLUSHED
			if (log_index_table_saved_before_promote(logindex_snapshot, table))
			{
				succeed = true;
				LOG_INDEX_MEM_TBL_SET_STATE(table, LOG_INDEX_MEM_TBL_STATE_FLUSHED);
			}
			else if (log_index_write_table(logindex_snapshot, table)) //XI: Write table data and bloom data to disk
				succeed = true;

			if (!succeed)
			{
				POLAR_LOG_LOGINDEX_META_INFO(meta);
				elog(FATAL, "Failed to save logindex table, table id=%ld", LOG_INDEX_MEM_TBL_TID(table));
			}
		}
	}

	/* Notify background process to flush logindex table */
	NOTIFY_LOGINDEX_BG_WORKER(logindex_snapshot->bg_worker_latch);
}

//XI: if the table is inactive, flush table data to disk (state:FLUSHED)
//      then memset this table to all 0 (state:FREE)
//      then use parameter lsn to initialize this table's prefix LSN (state:ACTIVE)
static void
log_index_wait_active(log_index_snapshot_t *logindex_snapshot, log_mem_table_t *table, XLogRecPtr lsn)
{
	LWLock     *lock;
	bool        end = false;

	Assert(table != NULL);
	lock = LOG_INDEX_MEM_TBL_LOCK(table);

	for (;;)
	{
		/*
		 * Wait table state changed from INACTIVE to ACTIVE.
		 */
		LWLockAcquire(lock, LW_EXCLUSIVE);

		/*
		 * We only save table to storage when polar_streaming_xlog_meta is true.
		 * If the table we are waiting is inactive then force to save it in this process.
		 */
        //XI: if this table is inactive, and snapshot is WRITABLE, save table data and bloom data to disk
        //      and set its state as FLUSHED
		if (LOG_INDEX_MEM_TBL_STATE(table) == LOG_INDEX_MEM_TBL_STATE_INACTIVE)
			log_index_force_save_table(logindex_snapshot, table);

        //XI: after this page is flushed, clear this table
		if (LOG_INDEX_MEM_TBL_STATE(table) == LOG_INDEX_MEM_TBL_STATE_FLUSHED)
			MemSet(table, 0, sizeof(log_mem_table_t));

        //XI: the state will be FREE (0x00) after memset(0)
        //XI: Set table state as ACTIVE, and set this table's prefix lsn, and set free_head as 1
		if (LOG_INDEX_MEM_TBL_STATE(table) == LOG_INDEX_MEM_TBL_STATE_FREE)
			LOG_INDEX_MEM_TBL_NEW_ACTIVE(table, lsn);

        //XI: If the previous processes are successful, it's time to break the loop
		if (LOG_INDEX_MEM_TBL_STATE(table) == LOG_INDEX_MEM_TBL_STATE_ACTIVE
				&& !LOG_INDEX_MEM_TBL_FULL(table))
			end = true;

		LWLockRelease(lock);

		if (end)
			break;

		if (InRecovery)
			HandleStartupProcInterrupts();
		else
			CHECK_FOR_INTERRUPTS();

		pg_usleep(10);
	}
}

// XI: iterate all the head with "key", (hash conflict)
// XI: if this page doesn't exist in this table, return value is NULL
static log_seg_id_t
log_index_mem_tbl_exists_page(BufferTag *tag,
							  log_idx_table_data_t *table, uint32 key)
{
    //XI: if the key doesn't exist in this table, then $exists is NULL
	log_seg_id_t    exists = LOG_INDEX_TBL_SLOT_VALUE(table, key);
	log_item_head_t *item;

    //XI: if the key doesn't exist in this page, then $item is NULL
	item = log_index_item_head(table, exists);

	while (item != NULL &&
			!BUFFERTAGS_EQUAL(item->tag, *tag))
	{
		exists = item->next_item;
		item = log_index_item_head(table, exists);
	}

	return exists;
}

//XI: Check whether node is full
//XI: Caller will depend on this to determine whether insert a new node
//XI: When the list's last node contains maximum records. (2 in head and 10 in segment)
static bool
log_index_mem_seg_full(log_mem_table_t *table, log_seg_id_t head)
{
	log_item_head_t *item;
	log_item_seg_t *seg;

	Assert(head != LOG_INDEX_TBL_INVALID_SEG);

	item = log_index_item_head(&table->data, head);

    // XI: the head list only has one head element
	if (item->tail_seg == head)
	{
		if (item->number == LOG_INDEX_ITEM_HEAD_LSN_NUM)
			return true;
	}
	else
	{
        // XI: The tail segments is No.($seg->number).
        // If it reached the maximum of this segment, return true
		seg = log_index_item_seg(&table->data, item->tail_seg);
		Assert(seg != NULL);

		if (seg->number == LOG_INDEX_ITEM_SEG_LSN_NUM)
			return true;
	}

	return false;
}

//XI: Insert a new page to LogIndex
//XI: Insert a new head into current active table
//XI: update active_table segment[] list (set new_item_id as a new head)
//XI: update active_table hash[] list, if no hash_conflict
static void
log_index_insert_new_item(log_index_lsn_t *lsn_info,
						  log_mem_table_t *table, uint32 key,
						  log_seg_id_t new_item_id)
{
    //XI: get segment[new_item_id] as new-head from the active table (already assigned in the caller by free_head++)
	log_item_head_t *new_item = log_index_item_head(&table->data, new_item_id);
	log_seg_id_t   *slot;

	Assert(key < LOG_INDEX_MEM_TBL_HASH_NUM);
    //XI: the hash[] will store the first segment_id inserting with same key
	slot = LOG_INDEX_TBL_SLOT(&table->data, key);

	new_item->head_seg = new_item_id;
	new_item->next_item = LOG_INDEX_TBL_INVALID_SEG;
	new_item->next_seg = LOG_INDEX_TBL_INVALID_SEG;
	new_item->tail_seg = new_item_id;
	memcpy(&(new_item->tag), lsn_info->tag, sizeof(BufferTag));
	new_item->number = 1;
	new_item->prev_page_lsn = lsn_info->prev_lsn;
    //XI: Set head Suffix LSN[0] as lsn_info.lsn's suffix LSN
	LOG_INDEX_INSERT_LSN_INFO(new_item, 0, lsn_info);

    //XI: If there are other pages have same key (in the same slot)
	if (*slot == LOG_INDEX_TBL_INVALID_SEG)
		*slot = new_item_id;
	else // XI: Create a new slot
	{
		new_item->next_item = *slot;
		*slot = new_item_id;
	}
}

//XI: Get table->seg[ $seg_id ] as a new segment node
//XI: add this new segment node in the head list
//XI: set $new_seg->suffix_lsn[0] = lsn_info.suffix_lsn
static void
log_index_insert_new_seg(log_mem_table_t *table, log_seg_id_t head,
						 log_seg_id_t seg_id, log_index_lsn_t *lsn_info)
{
	log_item_head_t *item = log_index_item_head(&table->data, head);
	log_item_seg_t *seg = log_index_item_seg(&table->data, seg_id);

	seg->head_seg = head;

    //XI: if the head's list have no other elements
    //      set head's next segment to seg_id
	if (item->tail_seg == head)
		item->next_seg = seg_id;
	else
	{
        // XI: Find the last segment of this head list
        //      and set last segment's next_seg as seg_id
		log_item_seg_t *pre_seg = log_index_item_seg(&table->data, item->tail_seg);

		if (pre_seg == NULL)
		{
			POLAR_LOG_LOGINDEX_MEM_TABLE_INFO(table);
			ereport(PANIC, (errmsg("The log index table is corrupted, the segment %d is NULL;head=%d, seg_id=%d",
								   item->tail_seg, head, seg_id)));
		}

		pre_seg->next_seg = seg_id;
	}

	seg->prev_seg = item->tail_seg;
	item->tail_seg = seg_id;

    // XI: now this segment is tail, set its tail as InValid
	seg->next_seg = LOG_INDEX_TBL_INVALID_SEG;
    // XI: Why number is 1?
	seg->number = 1;
    // XI: set this segment's lsn[0] as lsn_info.lsn(suffix)
	LOG_INDEX_INSERT_LSN_INFO(seg, 0, lsn_info);
}

//XI: if the head list only has one head element, append it to head node
//XI: else, append it to tail segment node
//XI: Before this function, caller function will check whether this list is full
//XI: return value idx is the position in suffix LSN list
static uint8
log_index_append_lsn(log_mem_table_t *table, log_seg_id_t head, log_index_lsn_t *lsn_info)
{
	log_item_head_t *item;
	log_item_seg_t  *seg;
	uint8           idx;

	Assert(head != LOG_INDEX_TBL_INVALID_SEG);

	item = log_index_item_head(&table->data, head);

    //XI: if the head list has no segment element, add suffix lsn to the head
	if (item->tail_seg == head)
	{
		Assert(item->number < LOG_INDEX_ITEM_HEAD_LSN_NUM);
		idx = item->number;
		LOG_INDEX_INSERT_LSN_INFO(item, idx, lsn_info);
		item->number++;
	}
	else
	{ //XI: find the tail node and insert suffix LSN
		seg = log_index_item_seg(&table->data, item->tail_seg);
		Assert(seg != NULL);
		Assert(seg->number < LOG_INDEX_ITEM_SEG_LSN_NUM);
		idx = seg->number;
		LOG_INDEX_INSERT_LSN_INFO(seg, idx, lsn_info);
		seg->number++;
	}

	return idx;
}

//XI: find the free segment from the active table list
//XI: return value is the $free_head when inserting into the current ACTIVE_TABLE
//XI: LOOP all the active_table in the mem_table list
//      if table is new, use it and insert the first segment
//      if table is full or old(lsn doesn't match), loop to next mem_table and
//          set it as inactive talbe, also update global variable(active_table id)
//      otherwise, adopt the current active table, return (active_table->free_head++)
static log_seg_id_t
log_index_next_free_seg(log_index_snapshot_t *logindex_snapshot, XLogRecPtr lsn, log_mem_table_t **active_table)
{
	log_seg_id_t    dst = LOG_INDEX_TBL_INVALID_SEG;
	log_mem_table_t *active;
	int next_mem_id = -1;

    //XI: iterate all the table in mem_table list
	for (;;)
	{
        //XI: get current active table using snapshot->active_table(int)
		active = LOG_INDEX_MEM_TBL_ACTIVE();

		if (LOG_INDEX_MEM_TBL_STATE(active) == LOG_INDEX_MEM_TBL_STATE_ACTIVE)
		{
			/*
			 * 1. However when we get a new active table, we don't know its data.prefix_lsn,
			 * we assign InvalidXLogRecPtr lsn to data.prefix_lsn, so we should
			 * distinguish which table is new without prefix_lsn, and reassign it
			 * 2. If active table is full or
			 * new lsn prefix is different than this table's lsn prefix
			 * we will allocate new active memory table.
			 */
            //XI: TBL_IS_NEW-> if all the info in active-table is unsetted
			if (LOG_INDEX_MEM_TBL_IS_NEW(active))
			{
                //XI: set table's prefix_lsn with the current parameter lsn
				LOG_INDEX_MEM_TBL_SET_PREFIX_LSN(active, lsn);
                //XI: return table's free_head++
				dst = LOG_INDEX_MEM_TBL_UPDATE_FREE_HEAD(active);
			}
			else if (LOG_INDEX_MEM_TBL_FULL(active) ||    // XI: if free-head reached the maximum
					 !LOG_INDEX_SAME_TABLE_LSN_PREFIX(&active->data, lsn)) //XI: if this table has different table prefix lsn
			{
                // XI: set this table as InActive
				LOG_INDEX_MEM_TBL_SET_STATE(active, LOG_INDEX_MEM_TBL_STATE_INACTIVE);
                // XI: Loop to next active table, (ACTIVE_ID+1) % (mem_table_size)
				next_mem_id = LOG_INDEX_MEM_TBL_NEXT_ID(LOG_INDEX_MEM_TBL_ACTIVE_ID);
			}
			else //XI: table's free head++
				dst = LOG_INDEX_MEM_TBL_UPDATE_FREE_HEAD(active);
		}

		if (dst != LOG_INDEX_TBL_INVALID_SEG)
			return dst;

		if (next_mem_id != -1)
		{
            // XI: change to new active table
			active = LOG_INDEX_MEM_TBL(next_mem_id);
			*active_table = active;

			NOTIFY_LOGINDEX_BG_WORKER(logindex_snapshot->bg_worker_latch);
		}

		pgstat_report_wait_start(WAIT_EVENT_LOGINDEX_WAIT_ACTIVE);
		log_index_wait_active(logindex_snapshot, active, lsn);
		pgstat_report_wait_end();

		if (next_mem_id != -1)
		{
			SpinLockAcquire(LOG_INDEX_SNAPSHOT_LOCK);
			LOG_INDEX_MEM_TBL_ACTIVE_ID = next_mem_id;
			SpinLockRelease(LOG_INDEX_SNAPSHOT_LOCK);
		}
	}

	/* never reach here */
	return LOG_INDEX_TBL_INVALID_SEG;
}

static log_file_table_bloom_t *
log_index_get_bloom_lru(log_index_snapshot_t *logindex_snapshot, log_idx_table_id_t tid, int *slot)
{
	int pageno = LOG_INDEX_TBL_BLOOM_PAGE_NO(tid);
	int offset = LOG_INDEX_TBL_BLOOM_PAGE_OFFSET(tid);
	SlruShared  shared = logindex_snapshot->bloom_ctl.shared;

	if (offset == 0)
		*slot = SimpleLruZeroPage(&logindex_snapshot->bloom_ctl, pageno);
	else
	{
		*slot = SimpleLruReadPage(&logindex_snapshot->bloom_ctl, pageno,
								  false, InvalidTransactionId);
	}

	return (log_file_table_bloom_t *)(shared->page_buffer[*slot] + offset);
}


log_file_table_bloom_t *
log_index_get_tbl_bloom(log_index_snapshot_t *logindex_snapshot, log_idx_table_id_t tid)
{
	int pageno = LOG_INDEX_TBL_BLOOM_PAGE_NO(tid);
	int offset = LOG_INDEX_TBL_BLOOM_PAGE_OFFSET(tid);
	SlruShared  shared = logindex_snapshot->bloom_ctl.shared;

	int slot;

	slot = SimpleLruReadPage_ReadOnly(&logindex_snapshot->bloom_ctl, pageno,
									  InvalidTransactionId);

	return (log_file_table_bloom_t *)(shared->page_buffer[slot] + offset);
}

// XI: Initialize bloom_filter in the bloom_bytes
// XI: and calculate $table's all the head node to this bloom_filter
static void
log_index_calc_bloom(log_mem_table_t *table, log_file_table_bloom_t *bloom)
{
	bloom_filter *filter;
	int i;

    // XI: initialize bloom_filter in the bloom_bytes
	filter = bloom_init_struct(bloom->bloom_bytes, bloom->buf_size,
							   LOG_INDEX_BLOOM_ELEMS_NUM, 0);

    // XI: iterate all the hash slot in the table
	for (i = 0; i < LOG_INDEX_MEM_TBL_HASH_NUM; i++)
	{
        // XI: $id is the segment id corresponding to this hash slot
        // XI: if there is no values in this slot, id is 0
		log_seg_id_t id = LOG_INDEX_TBL_SLOT_VALUE(&table->data, i);

        // XI: if this slot has a valid item
        // XI: traverse all the head in this slot (hash conflict) and add them to bloom_filter
		if (id != LOG_INDEX_TBL_INVALID_SEG)
		{
			log_item_head_t *item = log_index_item_head(&table->data, id);

			while (item != NULL)
			{
				bloom->max_lsn = Max(bloom->max_lsn,
									 log_index_item_max_lsn(&table->data, item));
				bloom->min_lsn =
					Min(bloom->min_lsn, LOG_INDEX_SEG_MIN_LSN(&table->data, item));
				bloom_add_element(filter, (unsigned char *) & (item->tag),
								  sizeof(BufferTag));
				item = log_index_item_head(&table->data, item->next_item);
			}
		}
	}
}

static bool
log_index_save_table(log_index_snapshot_t *logindex_snapshot, log_idx_table_data_t *table, File fd, log_file_table_bloom_t *bloom)
{
	int ret = -1;
    //XI: (tid)-1) / LOG_INDEX_TABLE_NUM_PER_FILE
	uint64 segno = LOG_INDEX_FILE_TABLE_SEGMENT_NO(table->idx_table_id);
    //XI: (((tid)-1) % LOG_INDEX_TABLE_NUM_PER_FILE) * sizeof(log_idx_table_data_t)
	off_t offset = LOG_INDEX_FILE_TABLE_SEGMENT_OFFSET(table->idx_table_id);
	char        path[MAXPGPATH];

	table->min_lsn = bloom->min_lsn;
	table->max_lsn = bloom->max_lsn;

	table->crc = 0;
	table->crc = log_index_calc_crc((unsigned char *)table, sizeof(log_idx_table_data_t));

	ret = polar_file_pwrite(fd, (char *)table, sizeof(*table), offset, WAIT_EVENT_LOGINDEX_TBL_WRITE);

	if (ret != sizeof(*table))
	{
		logindex_errno = errno;
		logindex_io_err = LOG_INDEX_WRITE_FAILED;

		LOG_INDEX_FILE_TABLE_NAME(path, segno);
		ereport(LOG,
				(errmsg("Could not write whole table to file \"%s\" at offset %lu, write size %d, errno %d",
						path, offset, ret, logindex_errno)));
		return false;
	}

	ret = FileSync(fd, WAIT_EVENT_LOGINDEX_TBL_FLUSH);

	if (ret != 0)
	{
		logindex_errno = errno;
		logindex_io_err = LOG_INDEX_FSYNC_FAILED;

		LOG_INDEX_FILE_TABLE_NAME(path, segno);
		ereport(LOG,
				(errmsg("Could not fsync file \"%s\", errno %d", path, logindex_errno)));

		return false;
	}

	return true;
}

static void
log_index_get_bloom_data(log_mem_table_t *table, log_idx_table_id_t tid, log_file_table_bloom_t *bloom)
{

	bloom->idx_table_id = tid;
	bloom->max_lsn = InvalidXLogRecPtr;
	bloom->min_lsn = UINT64_MAX;
    //XI: buf_size is the ($bloom_bytes) size
	bloom->buf_size = LOG_INDEX_FILE_TBL_BLOOM_SIZE -
					  offsetof(log_file_table_bloom_t, bloom_bytes);

    //XI: calculate all the table's head nodes' data to bloom->bloom_bytes
    //XI: the bloom->bloom_bytes has a bloom_filter
	log_index_calc_bloom(table, bloom);

	bloom->crc = 0;
	bloom->crc = log_index_calc_crc((unsigned char *)bloom, LOG_INDEX_FILE_TBL_BLOOM_SIZE);
}

// XI: Save bloom to disk file
// XI: Get the slur page corresponding to this table's bloom data
// XI: Write bloom data using slru
static void
log_index_save_bloom(log_index_snapshot_t *logindex_snapshot, log_idx_table_id_t tid, log_file_table_bloom_t *bloom)
{
	int slot;
	log_file_table_bloom_t *lru_bloom;
	SlruShared  shared = logindex_snapshot->bloom_ctl.shared;

	LWLockAcquire(LOG_INDEX_BLOOM_LRU_LOCK, LW_EXCLUSIVE);
	lru_bloom = log_index_get_bloom_lru(logindex_snapshot, tid, &slot);
	memcpy(lru_bloom, bloom, LOG_INDEX_FILE_TBL_BLOOM_SIZE);
	shared->page_dirty[slot] = true;
	/*
	 * If this tid write from offset=0, then this segment file does not exits,
	 * O_CREAT flag will be set to open this file.Otherwise we will open this segment file
	 * without O_CREAT flag to append bloom data.
	 */
	polar_slru_append_page(&logindex_snapshot->bloom_ctl, slot, LOG_INDEX_FILE_TABLE_SEGMENT_OFFSET(tid) != 0);
	LWLockRelease(LOG_INDEX_BLOOM_LRU_LOCK);
}

// XI: Calculate file name by table_id, then open it and return fd
// XI: logindex_snapshot is useless??
static int
log_index_open_table_file(log_index_snapshot_t *logindex_snapshot, log_idx_table_id_t tid, bool readonly, int elevel)
{
	char        path[MAXPGPATH];
	File fd;
	int flag;
	uint64 segno = LOG_INDEX_FILE_TABLE_SEGMENT_NO(tid);
	off_t offset = LOG_INDEX_FILE_TABLE_SEGMENT_OFFSET(tid);

    // XI: parse table name to $path
	LOG_INDEX_FILE_TABLE_NAME(path, segno);

	if (readonly)
		flag = O_RDONLY | PG_BINARY;
	else
	{
		flag = O_RDWR | PG_BINARY;

		if (offset == 0)
			flag |= O_CREAT;
	}

	fd = PathNameOpenFile(path, flag, true);

	if (fd < 0)
	{
		logindex_io_err = LOG_INDEX_OPEN_FAILED;
		logindex_errno = errno;

		ereport(elevel,
				(errmsg("Could not open file \"%s\", errno %d", path, logindex_errno)));
		return -1;
	}

	return fd;
}

// XI: Open table from file, read table data to parameter $table
bool
log_index_read_table_data(log_index_snapshot_t *logindex_snapshot, log_idx_table_data_t *table, log_idx_table_id_t tid, int elevel)
{
	File fd;
	pg_crc32 crc;
	int bytes;
	uint64 segno = LOG_INDEX_FILE_TABLE_SEGMENT_NO(tid);
	off_t offset = LOG_INDEX_FILE_TABLE_SEGMENT_OFFSET(tid);
	static char        path[MAXPGPATH];

	fd = log_index_open_table_file(logindex_snapshot, tid, true, elevel);

	if (fd < 0)
		return false;

	bytes = polar_file_pread(fd, (char *)table, sizeof(log_idx_table_data_t), offset, WAIT_EVENT_LOGINDEX_TBL_READ);

	if (bytes != sizeof(log_idx_table_data_t))
	{
		logindex_io_err = LOG_INDEX_READ_FAILED;
		logindex_errno = errno;
		FileClose(fd);

		LOG_INDEX_FILE_TABLE_NAME(path, segno);
		ereport(elevel,
				(errmsg("Could not read whole table from file \"%s\" at offset %lu, read size %d, errno %d",
						path, offset, bytes, logindex_errno)));
		return false;
	}

	FileClose(fd);
	crc = table->crc;
	table->crc = 0;
	table->crc = log_index_calc_crc((unsigned char *)table, sizeof(log_idx_table_data_t));

	if (crc != table->crc)
	{
		logindex_io_err = LOG_INDEX_CRC_FAILED;

		LOG_INDEX_FILE_TABLE_NAME(path, segno);
		ereport(elevel,
				(errmsg("The crc32 check failed in file \"%s\" at offset %lu, result crc %u, expected crc %u",
						path, offset, crc, table->crc)));
		return false;
	}

	return true;
}

// XI: 1. Calculate bloom data of this table
// XI: 2. Save bloom data to disk using slru
// XI: 3. Save and sync table data to disk
static bool
log_index_write_table_data(log_index_snapshot_t *logindex_snapshot, log_mem_table_t *table)
{
	bool ret = false;
	File fd;
	log_file_table_bloom_t *bloom;
	log_idx_table_id_t tid = table->data.idx_table_id;

	fd = log_index_open_table_file(logindex_snapshot, tid, false, polar_trace_logindex(DEBUG4));

	if (fd < 0)
		return ret;

	bloom = (log_file_table_bloom_t *)palloc0(LOG_INDEX_FILE_TBL_BLOOM_SIZE);

    //XI: calculate the bloom value of this table. (I think $table and $tid is duplicated, can ignore $tid)
    //XI: $bloom is a bloom_filter header, the bloom_filter is stored in $bloom->bloom_bytes
	log_index_get_bloom_data(table, tid, bloom);

	/*
	 * POLAR: we save bloom data before table data, in case that replica
	 * read bloom data with zero page
	 */
    //XI: Save this table's bloom data by slru
	log_index_save_bloom(logindex_snapshot, tid, bloom);
    //XI: Write and Sync this table's data to disk file
	ret = log_index_save_table(logindex_snapshot, &table->data, fd, bloom);
	pfree(bloom);

	FileClose(fd);

	return ret;
}

static void
log_index_report_io_error(log_index_snapshot_t *logindex_snapshot, log_idx_table_id_t tid)
{
	uint64 segno = LOG_INDEX_FILE_TABLE_SEGMENT_NO(tid);
	int offset = LOG_INDEX_FILE_TABLE_SEGMENT_OFFSET(tid);
	char        path[MAXPGPATH];

	LOG_INDEX_FILE_TABLE_NAME(path, segno);
	errno = logindex_errno;

	switch (logindex_io_err)
	{
		case LOG_INDEX_OPEN_FAILED:
			ereport(FATAL,
					(errcode_for_file_access(),
					 errmsg("Could not open file \"%s\" for tid=%ld", path, tid)));
			break;

		case LOG_INDEX_SEEK_FAILED:
			ereport(FATAL,
					(errcode_for_file_access(),
					 errmsg("Could not seek in file \"%s\" to offset %u for tid=%ld",
							path, offset, tid)));
			break;

		case LOG_INDEX_READ_FAILED:
			ereport(FATAL,
					(errcode_for_file_access(),
					 errmsg("Could not read from file \"%s\" at offset %u for tid=%ld",
							path, offset, tid)));
			break;

		case LOG_INDEX_WRITE_FAILED:
			ereport(FATAL,
					(errcode_for_file_access(),
					 errmsg("Could not write to file \"%s\" at offset %u for tid=%ld",
							path, offset, tid)));
			break;

		case LOG_INDEX_FSYNC_FAILED:
			ereport(FATAL,
					(errcode_for_file_access(),
					 errmsg("Could not fsync file \"%s\" for tid=%ld", path, tid)));
			break;

		case LOG_INDEX_CLOSE_FAILED:
			ereport(FATAL,
					(errcode_for_file_access(),
					 errmsg("Could not close file \"%s\" for tid=%ld", path, tid)));
			break;

		case LOG_INDEX_CRC_FAILED:
			ereport(FATAL,
					(errmsg("The crc32 check failed in file \"%s\" at offset %u for tid=%ld",
							path, offset, tid)));
			break;

		default:
			/* can't get here, we trust */
			elog(PANIC, "unrecognized LogIndex error cause: %d for tid=%ld",
				 (int) logindex_io_err, tid);
			break;
	}
}

static bool
log_index_read_seg_file(log_index_snapshot_t *logindex_snapshot, log_table_cache_t *cache, uint64 segno)
{
	int bytes;
	int i;
	log_index_meta_t meta;
	uint64_t delta_table;

	log_idx_table_data_t *table_data;

	LOG_INDEX_COPY_META(&meta);
	cache->min_idx_table_id = LOG_INDEX_TABLE_INVALID_ID;
	cache->max_idx_table_id = LOG_INDEX_TABLE_INVALID_ID;

    //XI: if max_idx_table_id > segno(file_num)* table/file
	delta_table = (meta.max_idx_table_id >= (segno * LOG_INDEX_TABLE_NUM_PER_FILE)) ?
				  meta.max_idx_table_id - (segno * LOG_INDEX_TABLE_NUM_PER_FILE) : 0;

	if (logindex_snapshot->segment_cache && delta_table >= LOG_INDEX_TABLE_NUM_PER_FILE)
	{
		polar_cache_io_error io_error;

		if (!polar_local_cache_read(
					logindex_snapshot->segment_cache, segno, 0,
					cache->data, LOG_INDEX_TABLE_CACHE_SIZE, &io_error))
		{
			/*no cover begin*/
			logindex_io_err = LOG_INDEX_READ_FAILED;
			logindex_errno = io_error.save_errno;
			polar_local_cache_report_error(logindex_snapshot->segment_cache, &io_error, LOG);
			return false;
			/*no cover end*/
		}

		bytes = LOG_INDEX_TABLE_CACHE_SIZE;
	}
	else
	{
		char   path[MAXPGPATH];
		File fd;

		LOG_INDEX_FILE_TABLE_NAME(path, segno);
		fd = PathNameOpenFile(path, O_RDONLY | PG_BINARY, true);

		if (fd < 0)
		{
			/*no cover begin*/
			logindex_io_err = LOG_INDEX_OPEN_FAILED;
			logindex_errno = errno;

			ereport(LOG, (errmsg("Could not open file \"%s\", errno %d", path, logindex_errno)));
			return false;
			/*no cover end*/
		}

		bytes = FileRead(fd, cache->data, LOG_INDEX_TABLE_CACHE_SIZE, WAIT_EVENT_LOGINDEX_TBL_READ);

		if (bytes < sizeof(log_idx_table_data_t))
		{
			/*no cover begin*/
			logindex_io_err = LOG_INDEX_READ_FAILED;
			logindex_errno = errno;
			FileClose(fd);

			ereport(LOG, (errmsg("Could not read whole table from file \"%s\" at offset 0, read size %d, errno %d",
								 path, bytes, logindex_errno)));
			return false;
			/*no cover end*/
		}

		FileClose(fd);
	}

	/* segno start from 0, while log_index_table_id_t start from 1 */
	cache->min_idx_table_id = segno * LOG_INDEX_TABLE_NUM_PER_FILE + 1;
	table_data = (log_idx_table_data_t *)cache->data;

	if (table_data->idx_table_id != cache->min_idx_table_id || cache->min_idx_table_id > meta.max_idx_table_id)
	{
		elog(WARNING, "Read unexpected logindex segment=%ld file, min_id=%ld, max_id=%ld, tid=%ld",
			 segno, cache->min_idx_table_id, meta.max_idx_table_id, table_data->idx_table_id);
		cache->min_idx_table_id = LOG_INDEX_TABLE_INVALID_ID;
		return false;
	}

	i = (bytes / sizeof(log_idx_table_data_t)) - 1;

	/*
	 * If this segment file is renamed from previous segment file, maybe there're old tables
	 * in the end of the file. So we have to compare to get max table id, and compare with meta to
	 * check it's already full flushed to the storage.
	 */
	while (i >= 0)
	{
		table_data = (log_idx_table_data_t *)(cache->data + sizeof(log_idx_table_data_t) * i);

		if (table_data->idx_table_id >= cache->min_idx_table_id && table_data->idx_table_id <= meta.max_idx_table_id)
		{
			cache->max_idx_table_id = table_data->idx_table_id;
			break;
		}

		i--;
	}

	return true;
}


/*
 * Read logindex table base on tid and return the table content.
 * If the return table content is from the logindex memory table,
 * then the output param *mem_table point to the table in logindex memory table, otherwise *mem_table is NULL.
 */
log_idx_table_data_t *
log_index_read_table(logindex_snapshot_t logindex_snapshot, log_idx_table_id_t tid, log_mem_table_t **mem_table)
{
    //XI: here table_cache is a static variable
	static log_table_cache_t table_cache;
	int mid = (tid - 1) % logindex_snapshot->mem_tbl_size;
	log_mem_table_t *table = LOG_INDEX_MEM_TBL(mid);
	LWLock *table_lock = LOG_INDEX_MEM_TBL_LOCK(table);
	log_idx_table_data_t    *data;

	*mem_table = NULL;

	/* Return table if it's already in shared memory */
	if (LWLockConditionalAcquire(table_lock, LW_SHARED))
	{
		if ((LOG_INDEX_MEM_TBL_STATE(table) == LOG_INDEX_MEM_TBL_STATE_FLUSHED) && (tid == LOG_INDEX_MEM_TBL_TID(table)))
		{
			*mem_table = table;
			return &table->data;
		}

		LWLockRelease(table_lock);
	}

    //XI: try to find it in the cache
	if ((strcmp(table_cache.name, logindex_snapshot->dir) != 0) ||
			tid < table_cache.min_idx_table_id || tid > table_cache.max_idx_table_id)
	{
        //XI: if it's not in the cache, read it from file to the cache
		if (!log_index_read_seg_file(logindex_snapshot, &table_cache, LOG_INDEX_FILE_TABLE_SEGMENT_NO(tid)))
		{
			log_index_report_io_error(logindex_snapshot, tid);
			return NULL;
		}

		strcpy(table_cache.name, logindex_snapshot->dir);
	}

	if (tid < table_cache.min_idx_table_id || tid > table_cache.max_idx_table_id)
		elog(PANIC, "Failed to read tid = %ld, while min_tid = %ld and max_tid = %ld",
			 tid, table_cache.min_idx_table_id, table_cache.max_idx_table_id);

	data = LOG_INDEX_GET_CACHE_TABLE(&table_cache, tid);

	/* Replace the table with the same position in shared memory and its state is FLUSHED */
	if (LWLockConditionalAcquire(table_lock, LW_EXCLUSIVE))
	{
		if (LOG_INDEX_MEM_TBL_STATE(table) == LOG_INDEX_MEM_TBL_STATE_FLUSHED && tid != LOG_INDEX_MEM_TBL_TID(table))
			memcpy(&table->data, data, sizeof(log_idx_table_data_t));

		LWLockRelease(table_lock);
	}

	return data;
}

//XI: write $table data and bloom data to disk
//XI: if there are previous table hasn't been written, just return
//XI: if this table is not an active table, also update the meta data in the disk
bool
log_index_write_table(log_index_snapshot_t *logindex_snapshot, log_mem_table_t *table)
{
	bool succeed = false;
	uint64 segment_no;
	log_idx_table_id_t tid;
	log_index_meta_t *meta = &logindex_snapshot->meta;
	log_index_file_segment_t *min_seg = &meta->min_segment_info;
	MemoryContext  oldcontext = MemoryContextSwitchTo(polar_logindex_memory_context()) ;

	tid = LOG_INDEX_MEM_TBL_TID(table);

	LWLockAcquire(LOG_INDEX_IO_LOCK, LW_EXCLUSIVE);

	/*
	 * Save logindex table base on the table id order
	 */
    //XI: writing table should one by one, if there are other previous tables haven't been written, return.
	if (tid == meta->max_idx_table_id + 1)
	{
        //XI: here really write table data and bloom data to disk
		if (!log_index_write_table_data(logindex_snapshot, table))
			log_index_report_io_error(logindex_snapshot, LOG_INDEX_MEM_TBL_TID(table));
		/* We don't update meta when flush active memtable */
		else if (LOG_INDEX_MEM_TBL_STATE(table) == LOG_INDEX_MEM_TBL_STATE_ACTIVE)
		{
			/* Flush active memtable, nothing to do */
			succeed = true;
		}
		else
		{
			SpinLockAcquire(LOG_INDEX_SNAPSHOT_LOCK);
			meta->max_idx_table_id = Max(meta->max_idx_table_id, tid);
			meta->max_lsn = Max(meta->max_lsn, table->data.max_lsn);
			SpinLockRelease(LOG_INDEX_SNAPSHOT_LOCK);

            //XI: this table will fall in segment_no file
			segment_no = LOG_INDEX_FILE_TABLE_SEGMENT_NO(tid);

			min_seg->segment_no = Min(min_seg->segment_no, segment_no);

            //XI: meta data saved the minimal file segment no.
            //XI: if this table is also included in this file, update the meta data
			if (min_seg->segment_no == segment_no)
			{
				min_seg->max_lsn = Max(table->data.max_lsn, min_seg->max_lsn);

				min_seg->max_idx_table_id = Max(tid, min_seg->max_idx_table_id);
				min_seg->min_idx_table_id = min_seg->segment_no * LOG_INDEX_TABLE_NUM_PER_FILE + 1;
			}

			polar_log_index_write_meta(logindex_snapshot, meta, true);

			succeed = true;
			LOG_INDEX_MEM_TBL_SET_STATE(table, LOG_INDEX_MEM_TBL_STATE_FLUSHED);
		}
	}

	LWLockRelease(LOG_INDEX_IO_LOCK);

	MemoryContextSwitchTo(oldcontext);

	return succeed;
}

static void
log_index_update_min_segment(log_index_snapshot_t *logindex_snapshot)
{
	log_index_meta_t            *meta = &logindex_snapshot->meta;
	log_index_file_segment_t    *min_seg = &meta->min_segment_info;

	min_seg->segment_no++;
	min_seg->min_idx_table_id = min_seg->segment_no * LOG_INDEX_TABLE_NUM_PER_FILE + 1;

	if (LOG_INDEX_FILE_TABLE_SEGMENT_NO(meta->max_idx_table_id) == min_seg->segment_no)
	{
		min_seg->max_idx_table_id = meta->max_idx_table_id;
		min_seg->max_lsn = meta->max_lsn;
	}
	else
	{
		log_idx_table_data_t *table = palloc(sizeof(log_idx_table_data_t));
		min_seg->max_idx_table_id = (min_seg->segment_no + 1) * LOG_INDEX_TABLE_NUM_PER_FILE;

		if (log_index_read_table_data(logindex_snapshot, table, min_seg->max_idx_table_id, polar_trace_logindex(DEBUG4)) == false)
		{
			POLAR_LOG_LOGINDEX_META_INFO(meta);
			ereport(PANIC,
					(errmsg("Failed to read log index which tid=%ld when truncate logindex",
							min_seg->max_idx_table_id)));
		}
		else
			min_seg->max_lsn = table->max_lsn;

		pfree(table);
	}


	polar_log_index_write_meta(logindex_snapshot, &logindex_snapshot->meta, true);
}

static bool
log_index_rename_segment_file(log_index_snapshot_t *logindex_snapshot, char *old_file)
{
	char new_file[MAXPGPATH];
	uint64 new_seg_no;
	uint64 max_seg_no;
	log_index_meta_t *meta = &logindex_snapshot->meta;
	int ret;

	LWLockAcquire(LOG_INDEX_IO_LOCK, LW_SHARED);
	max_seg_no = LOG_INDEX_FILE_TABLE_SEGMENT_NO(meta->max_idx_table_id);
	max_seg_no = Max(max_seg_no, logindex_snapshot->max_allocated_seg_no);
	new_seg_no = max_seg_no + 1;
	LOG_INDEX_FILE_TABLE_NAME(new_file, new_seg_no);

	ret = polar_durable_rename(old_file, new_file, LOG);

	if (ret == 0)
		logindex_snapshot->max_allocated_seg_no = new_seg_no;

	LWLockRelease(LOG_INDEX_IO_LOCK);

	if (ret == 0)
		elog(LOG, "logindex rename %s to %s", old_file, new_file);

	return ret == 0;
}

static bool
log_index_truncate(log_index_snapshot_t *logindex_snapshot, XLogRecPtr lsn)
{
	log_index_meta_t            *meta = &logindex_snapshot->meta;
	log_index_file_segment_t    *min_seg = &meta->min_segment_info;
	uint64                      bloom_page;
	char                        path[MAXPGPATH];
	uint64                      min_segment_no;
	uint64                      max_segment_no;
	log_idx_table_id_t          max_unused_tid;

	LWLockAcquire(LOG_INDEX_IO_LOCK, LW_EXCLUSIVE);

	if (meta->crc == 0 || XLogRecPtrIsInvalid(meta->max_lsn)
			|| XLogRecPtrIsInvalid(min_seg->max_lsn)
			|| min_seg->max_lsn >= lsn)
	{
		LWLockRelease(LOG_INDEX_IO_LOCK);
		return false;
	}

	Assert(LOG_INDEX_FILE_TABLE_SEGMENT_NO(meta->max_idx_table_id) >= min_seg->segment_no);
	Assert(meta->max_idx_table_id >= min_seg->max_idx_table_id);

	/* Keep last saved segment file */
	if (LOG_INDEX_FILE_TABLE_SEGMENT_NO(meta->max_idx_table_id) == min_seg->segment_no)
	{
		LWLockRelease(LOG_INDEX_IO_LOCK);
		return false;
	}

	/*
	 * Update meta first. If meta update succeed but fail to remove files, we will not read these files.
	 * Otherwise if we remove files succeed but fail to update meta, we will fail to read file base on meta data.
	 */
	max_segment_no = LOG_INDEX_FILE_TABLE_SEGMENT_NO(meta->max_idx_table_id);
	min_segment_no = min_seg->segment_no;
	max_unused_tid = min_seg->max_idx_table_id;
	log_index_update_min_segment(logindex_snapshot);
	max_segment_no = Max(logindex_snapshot->max_allocated_seg_no, max_segment_no);
	LWLockRelease(LOG_INDEX_IO_LOCK);

	LOG_INDEX_FILE_TABLE_NAME(path, min_segment_no);
	bloom_page = LOG_INDEX_TBL_BLOOM_PAGE_NO(max_unused_tid);
	elog(LOG, "logindex truncate bloom id=%ld page=%ld", max_unused_tid, bloom_page);

	SimpleLruTruncate(&logindex_snapshot->bloom_ctl, bloom_page);

	if (max_segment_no - min_segment_no < polar_max_logindex_files)
	{
		/* Rename unused file for next segment */
		if (log_index_rename_segment_file(logindex_snapshot, path))
			return true;
	}

	durable_unlink(path, LOG);

	return true;
}

//XI: keep truncating the files until the last created file
void
polar_logindex_truncate(log_index_snapshot_t *logindex_snapshot, XLogRecPtr lsn)
{
	if (!XLogRecPtrIsInvalid(lsn))
	{
		MemoryContext oldcontext = MemoryContextSwitchTo(polar_logindex_memory_context());

		while (log_index_truncate(logindex_snapshot, lsn))
			;

		MemoryContextSwitchTo(oldcontext);

		elog(LOG, "Truncate logindex %s from lsn=%lX", logindex_snapshot->dir, lsn);
	}
}

//XI: This function only return true when the last table's last LSN equal to parameter $lsn_info.lsn and page_tag matches
static bool
log_index_exists_in_saved_table(log_index_snapshot_t *logindex_snapshot, log_index_lsn_t *lsn_info)
{
	uint32 mid;
	log_mem_table_t *table;
	uint32 i;
	BufferTag      tag;
	log_index_lsn_t saved_lsn;

    //XI: Change to the previous active table in the mem_table list
	SpinLockAcquire(LOG_INDEX_SNAPSHOT_LOCK);
	mid = LOG_INDEX_MEM_TBL_PREV_ID(LOG_INDEX_MEM_TBL_ACTIVE_ID);
	SpinLockRelease(LOG_INDEX_SNAPSHOT_LOCK);

	table = LOG_INDEX_MEM_TBL(mid);

	if (LOG_INDEX_MEM_TBL_STATE(table) != LOG_INDEX_MEM_TBL_STATE_FLUSHED)
		return false;

	CLEAR_BUFFERTAG(tag);

	saved_lsn.tag = &tag;

	for (i = table->data.last_order; i > 0; i--)
	{
        //XI: if the table's order[i-1]'s LSN is not what we expected, return false
		if (log_index_get_order_lsn(&table->data, i - 1, &saved_lsn) != lsn_info->lsn)
			return false;

        //XI: if the LSN is we expected and the tags matches
		if (BUFFERTAGS_EQUAL(*(lsn_info->tag), *(saved_lsn.tag)))
			return true;
	}

	return false;
}

//XI: find a free space to insert a LSN
//XI: if the current table is full, loop to another table in mem_table list, change active table
//XI: if the active-table doesn't have this page before, insert a new head node
//XI:   else (current table has this page and record is not full in the tail node), append lsn to tail node
//XI: Also, update table and snapshot's max-min LSN info.
void
log_index_insert_lsn(log_index_snapshot_t *logindex_snapshot, log_index_lsn_t *lsn_info,  uint32 key)
{
	log_mem_table_t     *active = NULL;
	bool                new_item;
	log_seg_id_t        head = LOG_INDEX_TBL_INVALID_SEG;;

	Assert(lsn_info->prev_lsn < lsn_info->lsn);

	active = LOG_INDEX_MEM_TBL_ACTIVE();

	/*
	 * 1. Logindex table state is atomic uint32, it's safe to change state without table lock
	 * 2. Only one process insert lsn, so it's safe to check exists page without hash lock
	 */
    //XI: if the page doesn't exist in active table, head==NULL.
	if (LOG_INDEX_MEM_TBL_STATE(active) == LOG_INDEX_MEM_TBL_STATE_ACTIVE &&
			LOG_INDEX_SAME_TABLE_LSN_PREFIX(&active->data, lsn_info->lsn))
		head = log_index_mem_tbl_exists_page(lsn_info->tag, &active->data, key);

	new_item = (head == LOG_INDEX_TBL_INVALID_SEG);

    // XI: if the page exists in the list and list isn't full
	if (!new_item && !log_index_mem_seg_full(active, head))
	{
		uint8 idx;
		log_item_head_t *item;

        //XI: append a lsn record to an already exists node (which is not full)
		LWLockAcquire(LOG_INDEX_HASH_LOCK(key), LW_EXCLUSIVE);
		idx = log_index_append_lsn(active, head, lsn_info);
		item = log_index_item_head(&active->data, head);
        //XI: update idx_mem_table's order list
        //XI: append "segID&0FFF | (idx<<12)&F000" to the order list
		LOG_INDEX_MEM_TBL_ADD_ORDER(&active->data, item->tail_seg, idx);
		LWLockRelease(LOG_INDEX_HASH_LOCK(key));
	}
	else
	{
		log_seg_id_t    dst;
		log_mem_table_t *old_active = active;

        //XI: dst is the free_head value in the current active_table
        //XI: in this function, the active table may change, which means old_active!=active
		dst = log_index_next_free_seg(logindex_snapshot, lsn_info->lsn, &active);

		Assert(dst != LOG_INDEX_TBL_INVALID_SEG);

		LWLockAcquire(LOG_INDEX_HASH_LOCK(key), LW_EXCLUSIVE);

        //XI: if the page doesn't exist in the current active table
        //      or page exists in this current active table, however this table($old_active) is full
        //      or both dost exists in this table and table($old_active) is full
        //    then insert a new head in the current active-table
		if (new_item || active != old_active)
			log_index_insert_new_item(lsn_info, active, key, dst);
		else //XI: find free space in old_active table, occupy table.seg[dst] as new segment node
			log_index_insert_new_seg(active, head, dst, lsn_info);

		LOG_INDEX_MEM_TBL_ADD_ORDER(&active->data, dst, 0);
		LWLockRelease(LOG_INDEX_HASH_LOCK(key));
	}

	SpinLockAcquire(LOG_INDEX_SNAPSHOT_LOCK);
	active->data.max_lsn = Max(lsn_info->lsn, active->data.max_lsn);
	active->data.min_lsn = Min(lsn_info->lsn, active->data.min_lsn);
	logindex_snapshot->max_lsn = active->data.max_lsn;
	SpinLockRelease(LOG_INDEX_SNAPSHOT_LOCK);
}

void
polar_logindex_add_lsn(log_index_snapshot_t *logindex_snapshot, BufferTag *tag, XLogRecPtr prev, XLogRecPtr lsn)
{
	uint32      key = LOG_INDEX_MEM_TBL_HASH_PAGE(tag);
	log_index_meta_t *meta = NULL;
	log_index_lsn_t lsn_info;

	Assert(tag != NULL);
	Assert(lsn > prev);

	meta = &logindex_snapshot->meta;

	lsn_info.tag = tag;
	lsn_info.lsn = lsn;
	lsn_info.prev_lsn = prev;

    //XI: if the state is not ADDING, maybe INITIALIZED??
	if (unlikely(!polar_logindex_check_state(logindex_snapshot, POLAR_LOGINDEX_STATE_ADDING)))
	{
		/* Insert logindex from meta->start_lsn, so We don't save logindex which lsn is less then meta->start_lsn */
		if (lsn < meta->start_lsn)
			return;

		/*
		 * If log index initialization is not finished
		 * we don't save lsn if it's less than max saved lsn,
		 * which means it's already in saved table
		 */
		if (lsn < meta->max_lsn)
			return;

		/*
		 * If lsn is equal to max saved lsn then
		 * we check whether the tag is in saved table
		 */
        //XI: this function check whether previous table (active_id-1)'s the last record
        //      if what we want (LSN matches and page_tag matches).
		if (meta->max_lsn == lsn
				&& log_index_exists_in_saved_table(logindex_snapshot, &lsn_info))
			return;

		/*
		 * If we come here which means complete to check lsn overlap
		 * then we can save lsn to logindex memory table
		 */
		pg_atomic_fetch_or_u32(&logindex_snapshot->state, POLAR_LOGINDEX_STATE_ADDING);
		elog(LOG, "%s log index is insert from %lx", logindex_snapshot->dir, lsn);
	}

    //XI: Insert a new segment to active table (or append lsn to not full node),
    //      this process may include changing active table.
	log_index_insert_lsn(logindex_snapshot, &lsn_info, key);

	if (unlikely(polar_trace_logindex_messages <= DEBUG4))
	{
		log_mem_table_t *active = LOG_INDEX_MEM_TBL_ACTIVE();
		uint32 last_order = active->data.last_order;

		ereport(LOG, (errmsg("%s add %lX, t=%ld, o=%d, i=%d, f=%d, s=%d " POLAR_LOG_BUFFER_TAG_FORMAT,
							 logindex_snapshot->dir,
							 lsn,
							 active->data.idx_table_id,
							 last_order,
							 active->data.idx_order[last_order - 1],
							 active->free_head,
							 pg_atomic_read_u32(&active->state),
							 POLAR_LOG_BUFFER_TAG(tag)),
					  errhidestmt(true),
					  errhidecontext(true)));
	}
}

//XI: Find a page in $table.
//  If found, return its head node
//  Otherwise, return NULL
log_item_head_t *
log_index_tbl_find(BufferTag *tag,
				   log_idx_table_data_t *table, uint32 key)
{
	log_seg_id_t    item_id;

	Assert(table != NULL);

	item_id = log_index_mem_tbl_exists_page(tag, table, key);
	return log_index_item_head(table, item_id);
}

//XI: return the logindex_snapshot->max_lsn with lock involved
XLogRecPtr
polar_get_logindex_snapshot_max_lsn(log_index_snapshot_t *logindex_snapshot)
{
	XLogRecPtr  max_lsn = InvalidXLogRecPtr;

	SpinLockAcquire(LOG_INDEX_SNAPSHOT_LOCK);
	max_lsn = logindex_snapshot->max_lsn;
	SpinLockRelease(LOG_INDEX_SNAPSHOT_LOCK);
	return max_lsn;
}

/*
 * POLAR: load flushed/active tables from storages
 */
//XI: load at most mem_tbl_size table from disk to snapshot
//XI: Start a new active table
//TODO
void
polar_load_logindex_snapshot_from_storage(log_index_snapshot_t *logindex_snapshot, XLogRecPtr start_lsn)
{
	log_index_meta_t *meta = &logindex_snapshot->meta;
	log_idx_table_id_t new_max_idx_table_id = LOG_INDEX_TABLE_INVALID_ID;
	log_mem_table_t *active = LOG_INDEX_MEM_TBL_ACTIVE();
	log_mem_table_t *mem_tbl = NULL;
	static log_idx_table_data_t table;
	int mid = 0;
	log_idx_table_id_t tid = 0, min_tid = 0;
	uint32 state = pg_atomic_read_u32(&logindex_snapshot->state);

	/*
	 * If it's RW node, we only load tables whose min_lsn is less than start_lsn.
	 * But if we enable wal prefetch, we will create lsn iterator during
	 * recovery, so loading flushed table into memory can improve performance
	 * in some degree.
	 * If it's ro node, we will load all saved table from max_idx_table_id to memory table.
	 * It's optimization for the following page iterator, saving time to load table from storage.
	 */

	LWLockAcquire(LOG_INDEX_IO_LOCK, LW_EXCLUSIVE);

    //XI: read the meta data file from the disk
	if (log_index_get_meta(logindex_snapshot, meta))
		new_max_idx_table_id = meta->max_idx_table_id;

	LWLockRelease(LOG_INDEX_IO_LOCK);

	/* No table in storage */
	if (new_max_idx_table_id == LOG_INDEX_TABLE_INVALID_ID)
		return;

	/*
	 * POLAR: if we are initializing now, we load tables from big to small
	 * we cannot load all tables, because memtable is limited, so we should
	 * calculate min table to load
	 */
    //XI: if it's initializing, load the latest snapshot->mem_tbl_size tables
	if (!(state & POLAR_LOGINDEX_STATE_INITIALIZED))
	{
		Assert(!XLogRecPtrIsInvalid(start_lsn));

		/* we load at most mem_tbl_size tables */
        //XI: Load mem_tbl_size or fewer tables from storage
		if (new_max_idx_table_id > logindex_snapshot->mem_tbl_size)
			min_tid = Max(new_max_idx_table_id - logindex_snapshot->mem_tbl_size + 1,
						  meta->min_segment_info.min_idx_table_id);
		else
			min_tid = meta->min_segment_info.min_idx_table_id;

		/* min_segment_info.min_idx_table_id = 0 ? */
		if (min_tid == LOG_INDEX_TABLE_INVALID_ID)
			min_tid = new_max_idx_table_id;
	}
	else // XI: if the state is INITIALIZED, log from snapshot->max_tid to snapshot->max_tid + mem_tbl_size
	{
		/*
		 * When db start, there is no table to load, so active table_id is
		 * still invalid, at this situation, we should assign tid to active
		 * table(tid = 1)
		 */
        //XI: at db start, this table_id is invalid (just initialized), initialize this table as ACTIVE
        //      and tid as snapshot->max_tid
		if (LOG_INDEX_MEM_TBL_TID(active) == LOG_INDEX_TABLE_INVALID_ID)
			log_index_wait_active(logindex_snapshot, active, InvalidXLogRecPtr);

		min_tid = LOG_INDEX_MEM_TBL_TID(active);
		/* We cannot wrap active table slot, so limit max tid to load */
		new_max_idx_table_id = Min(new_max_idx_table_id,
								   min_tid + logindex_snapshot->mem_tbl_size - 1);
	}

	Assert(min_tid != LOG_INDEX_TABLE_INVALID_ID);

    //XI: load table from min_tid to new_max_idx_table_id, clear the old bloom data
    //XI: append a new active table after new_max_idx_table_id
	/* If we have more flushed tables to loaded */
	if (new_max_idx_table_id >= min_tid)
	{
		/* tid from big to small */
		tid = new_max_idx_table_id;

		while (tid >= min_tid)
		{
            //XI: transfer tid to mem_tbl_id
			mid = (tid - 1) % logindex_snapshot->mem_tbl_size;
			mem_tbl = LOG_INDEX_MEM_TBL(mid);

			/* POLAR: mark current memory table FLUSHED */
			LWLockAcquire(LOG_INDEX_MEM_TBL_LOCK(mem_tbl), LW_EXCLUSIVE);
			log_index_read_table_data(logindex_snapshot, &table, tid, LOG);
			memcpy(&mem_tbl->data, &table, sizeof(log_idx_table_data_t));
			LOG_INDEX_MEM_TBL_SET_STATE(mem_tbl, LOG_INDEX_MEM_TBL_STATE_FLUSHED);
			LOG_INDEX_MEM_TBL_FREE_HEAD(mem_tbl) = LOG_INDEX_MEM_TBL_SEG_NUM;
			polar_logindex_invalid_bloom_cache(logindex_snapshot, tid);
			LWLockRelease(LOG_INDEX_MEM_TBL_LOCK(mem_tbl));

			Assert(table.idx_table_id == tid);
			tid--;

			if (!XLogRecPtrIsInvalid(start_lsn) &&
					start_lsn >= table.min_lsn)
				break;
		}

		SpinLockAcquire(LOG_INDEX_SNAPSHOT_LOCK);
		/* Switch to the old active table */
		LOG_INDEX_MEM_TBL_ACTIVE_ID = (new_max_idx_table_id - 1) % logindex_snapshot->mem_tbl_size;
		active = LOG_INDEX_MEM_TBL_ACTIVE();
		logindex_snapshot->max_idx_table_id = new_max_idx_table_id;
		logindex_snapshot->max_lsn = active->data.max_lsn;
		/* Switch to the new active table */
		LOG_INDEX_MEM_TBL_ACTIVE_ID = new_max_idx_table_id % logindex_snapshot->mem_tbl_size;
		active = LOG_INDEX_MEM_TBL_ACTIVE();
		SpinLockRelease(LOG_INDEX_SNAPSHOT_LOCK);

		/* wait active to become available */
		log_index_wait_active(logindex_snapshot, active, InvalidXLogRecPtr);
	}

	/*
	 * If logindex is initialized we will try to read active table data from storage.
	 * When we flush active table data to storage we will not update logindex meta
	 */
	if (!(state & POLAR_LOGINDEX_STATE_INITIALIZED))
		return;

	Assert(active->data.idx_table_id != LOG_INDEX_TABLE_INVALID_ID);

	/*
	 * Read active mem table, maybe table has been reused, so must make sure
	 * table.idx_table_id == read_idx_table_id
	 */
	if (log_index_read_table_data(logindex_snapshot, &table, LOG_INDEX_MEM_TBL_TID(active), polar_trace_logindex(DEBUG4)) &&
			table.idx_table_id == LOG_INDEX_MEM_TBL_TID(active))
	{
		/* Table data in storage is fresh */
		if (table.max_lsn > active->data.max_lsn)
		{
			LWLockAcquire(LOG_INDEX_MEM_TBL_LOCK(active), LW_EXCLUSIVE);
			memcpy(&active->data, &table, sizeof(log_idx_table_data_t));
			LWLockRelease(LOG_INDEX_MEM_TBL_LOCK(active));
		}

		SpinLockAcquire(LOG_INDEX_SNAPSHOT_LOCK);
		Assert(active->data.max_lsn >= logindex_snapshot->max_lsn);
		logindex_snapshot->max_idx_table_id = LOG_INDEX_MEM_TBL_TID(active);
		logindex_snapshot->max_lsn = active->data.max_lsn;
		SpinLockRelease(LOG_INDEX_SNAPSHOT_LOCK);

		/* When we read active memtable from storage, maybe free_head is too old */
		while (!LOG_INDEX_MEM_TBL_FULL(active))
		{
			log_item_head_t *item = log_index_item_head(&active->data, LOG_INDEX_MEM_TBL_FREE_HEAD(active));

			if (item == NULL || item->head_seg == LOG_INDEX_TBL_INVALID_SEG)
				break;

			LOG_INDEX_MEM_TBL_UPDATE_FREE_HEAD(active);
		}
	}
}


uint64
polar_logindex_mem_tbl_size(logindex_snapshot_t logindex_snapshot)
{
	return logindex_snapshot != NULL ? logindex_snapshot->mem_tbl_size : 0;
}

//XI: snapshot->max_tid - meta->max_tid
uint64
polar_logindex_used_mem_tbl_size(logindex_snapshot_t logindex_snapshot)
{
	log_idx_table_id_t mem_tbl_size = 0;

	if (logindex_snapshot != NULL)
	{
		LWLockAcquire(LOG_INDEX_IO_LOCK, LW_SHARED);
		SpinLockAcquire(LOG_INDEX_SNAPSHOT_LOCK);
		mem_tbl_size = logindex_snapshot->max_idx_table_id -
					   logindex_snapshot->meta.max_idx_table_id;
		SpinLockRelease(LOG_INDEX_SNAPSHOT_LOCK);
		LWLockRelease(LOG_INDEX_IO_LOCK);
	}

	return mem_tbl_size;
}

uint64
polar_logindex_convert_mem_tbl_size(uint64 mem_size)
{
	return (mem_size * 1024L * 1024L) / (sizeof(log_mem_table_t) + sizeof(LWLockMinimallyPadded));
}

const char *
polar_get_logindex_snapshot_dir(logindex_snapshot_t logindex_snapshot)
{
	return logindex_snapshot->dir;
}

//XI: read disk's minimal lsn
//XI: use meta->min_seg to get the oldest table in the disk, then return $table->min_lsn
XLogRecPtr
polar_get_logindex_snapshot_storage_min_lsn(logindex_snapshot_t logindex_snapshot)
{
	log_index_meta_t            *meta = &logindex_snapshot->meta;
	log_index_file_segment_t    *min_seg = &meta->min_segment_info;
	log_idx_table_data_t *table = NULL;
	XLogRecPtr min_lsn = InvalidXLogRecPtr;

	table = palloc(sizeof(log_idx_table_data_t));

	LWLockAcquire(LOG_INDEX_IO_LOCK, LW_SHARED);

	if (min_seg->min_idx_table_id != LOG_INDEX_TABLE_INVALID_ID)
	{
		if (log_index_read_table_data(logindex_snapshot, table, min_seg->min_idx_table_id, LOG) == false)
		{
			POLAR_LOG_LOGINDEX_META_INFO(meta);
			ereport(PANIC,
					(errmsg("Failed to read log index which tid=%ld when truncate logindex",
							min_seg->min_idx_table_id)));
		}

		min_lsn = table->min_lsn;
	}

	LWLockRelease(LOG_INDEX_IO_LOCK);
	pfree(table);

	return min_lsn;
}

//XI: Set SlruShared->polar_ro_promoting = true
//XI: Set snapshot->state WRITABLE
//XI: Updating states from Inactive to Flushed, iterating from meta->max_saved_tid to mem_tbl->max_tid
//TODO
void
polar_logindex_online_promote(logindex_snapshot_t logindex_snapshot)
{
	log_index_meta_t *meta = &logindex_snapshot->meta;
	SlruShared shared = logindex_snapshot->bloom_ctl.shared;
	log_index_promoted_info_t *promoted_info = &logindex_snapshot->promoted_info;
	log_idx_table_id_t max_saved_tid = LOG_INDEX_TABLE_INVALID_ID;

	LWLockAcquire(LOG_INDEX_IO_LOCK, LW_EXCLUSIVE);

	if (log_index_get_meta(logindex_snapshot, meta))
	{
		promoted_info->old_rw_saved_max_lsn = meta->max_lsn;
		promoted_info->old_rw_saved_max_tid = meta->max_idx_table_id;
		promoted_info->old_rw_max_tid = meta->max_idx_table_id;

		max_saved_tid = meta->max_idx_table_id;
	}
	else
		elog(FATAL, "Failed to read logindex meta from shared storage");

	shared->polar_ro_promoting = true;
	pg_atomic_fetch_or_u32(&logindex_snapshot->state, POLAR_LOGINDEX_STATE_WRITABLE);
	LWLockRelease(LOG_INDEX_IO_LOCK);

	/* Force to update logindex table which is inactive to be flushed */
	log_index_update_ro_table_state(logindex_snapshot, max_saved_tid);

	elog(LOG, "Logindex %s is promoted", logindex_snapshot->dir);
	POLAR_LOG_LOGINDEX_META_INFO(meta);
}

//XI: if snapshot->meta.start_lsn is valid, return it
//XI: otherwise, if reach consistency in replica node, read meta from disk
XLogRecPtr
polar_logindex_check_valid_start_lsn(logindex_snapshot_t logindex_snapshot)
{
	log_index_meta_t *meta = &logindex_snapshot->meta;
	XLogRecPtr start_lsn = InvalidXLogRecPtr;

	LWLockAcquire(LOG_INDEX_IO_LOCK, LW_EXCLUSIVE);

	if (!XLogRecPtrIsInvalid(meta->start_lsn))
		start_lsn = meta->start_lsn;
	else if (InRecovery && reachedConsistency)
	{
		/*
		 * When reach consistency in replica node, read meta from storage is meta start lsn is invalid
		 */
		if (!polar_logindex_check_state(logindex_snapshot, POLAR_LOGINDEX_STATE_WRITABLE))
		{
			if (log_index_get_meta(logindex_snapshot, meta))
				start_lsn = meta->start_lsn;
			else
				elog(FATAL, "Failed to read logindex meta from shared storage");
		}
	}

	LWLockRelease(LOG_INDEX_IO_LOCK);

	return start_lsn;
}

//XI: set snapshot->meta.start_lsn and update disk meta
void
polar_logindex_set_start_lsn(logindex_snapshot_t logindex_snapshot, XLogRecPtr start_lsn)
{
	log_index_meta_t *meta = &logindex_snapshot->meta;

	Assert(!XLogRecPtrIsInvalid(start_lsn));

	LWLockAcquire(LOG_INDEX_IO_LOCK, LW_EXCLUSIVE);
	meta->start_lsn = start_lsn;
	polar_log_index_write_meta(logindex_snapshot, meta, false);
	LWLockRelease(LOG_INDEX_IO_LOCK);
}

XLogRecPtr
polar_logindex_mem_table_max_lsn(struct log_mem_table_t *table)
{
	return table->data.max_lsn;
}

//XI: create cache to snapshot->segment_cache and move the old local cache to trash dir
void
polar_logindex_create_local_cache(logindex_snapshot_t logindex_snapshot, const char *cache_name, uint32 max_segments)
{
	uint32 io_permission = POLAR_CACHE_LOCAL_FILE_READ | POLAR_CACHE_LOCAL_FILE_WRITE |
						   POLAR_CACHE_SHARED_FILE_READ;

	logindex_snapshot->segment_cache = polar_create_local_cache(cache_name, logindex_snapshot->dir,
																max_segments, LOG_INDEX_TABLE_NUM_PER_FILE * sizeof(log_idx_table_data_t),
																LWTRANCHE_POLAR_LOGINDEX_LOCAL_CACHE, io_permission, polar_logindex_local_cache_seg2str);
	/* POLAR: remove local cache file after create local cache */
	if (logindex_snapshot->segment_cache)
		polar_local_cache_move_trash(logindex_snapshot->segment_cache->dir_name);
}

void
polar_logindex_set_writer_latch(logindex_snapshot_t logindex_snapshot, struct Latch *latch)
{
	logindex_snapshot->bg_worker_latch = latch;
}

int
polar_trace_logindex(int trace_level)
{
	if (trace_level < LOG &&
			trace_level >= polar_trace_logindex_messages)
		return LOG;

	return trace_level;
}

//XI: update promoted_info's last inserted lsn
void
polar_logindex_update_promoted_info(logindex_snapshot_t logindex_snapshot, XLogRecPtr last_replayed_lsn)
{
	log_index_promoted_info_t *info = &logindex_snapshot->promoted_info;

	info->old_rw_max_inserted_lsn = last_replayed_lsn;
	info->old_rw_max_tid = logindex_snapshot->max_idx_table_id;
}
