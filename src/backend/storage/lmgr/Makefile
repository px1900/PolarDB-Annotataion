#-------------------------------------------------------------------------
#
# Makefile--
#    Makefile for storage/lmgr
#
# IDENTIFICATION
#    src/backend/storage/lmgr/Makefile
#
#-------------------------------------------------------------------------

subdir = src/backend/storage/lmgr
top_builddir = ../../../..
include $(top_builddir)/src/Makefile.global

OBJS = lmgr.o lock.o proc.o deadlock.o lwlock.o lwlocknames.o spin.o \
	s_lock.o predicate.o condition_variable.o polar_lock_stats.o

include $(top_srcdir)/src/backend/common.mk

ifdef TAS
TASPATH = $(top_builddir)/src/backend/port/tas.o
endif

# POLAR: use -march=armv8-a+lse if possible
s_lock.o: CFLAGS+=$(POLAR_CFLAGS_ARMV8_LSE)
# POLAR end

s_lock_test: s_lock.c $(top_builddir)/src/port/libpgport.a
	$(CC) $(CPPFLAGS) $(CFLAGS) -DS_LOCK_TEST=1 $(srcdir)/s_lock.c \
		$(TASPATH) -L $(top_builddir)/src/port -lpgport -o s_lock_test

# see notes in src/backend/parser/Makefile
lwlocknames.c: lwlocknames.h
	touch $@

lwlocknames.h: $(top_srcdir)/src/backend/storage/lmgr/lwlocknames.txt generate-lwlocknames.pl
	$(PERL) $(srcdir)/generate-lwlocknames.pl $<

check: s_lock_test
	./s_lock_test

clean distclean:
	rm -f s_lock_test

maintainer-clean: clean
	rm -f lwlocknames.h lwlocknames.c
