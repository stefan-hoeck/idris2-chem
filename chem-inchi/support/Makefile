TARGET = idris2_inchi
TARGET_VERSION ?= 0.0.1

INSTALLDIR  = ../lib
INSTALLDIR2 = ../../lib

LDFLAGS = -linchi
CPPFLAGS =

CC_VERSION = $(shell $(CC) --version)

ifeq ($(findstring clang,$(CC_VERSION)),clang)
 DYLIB_WORKAROUND = cp "${INSTALLDIR}/${TARGET}" "${INSTALLDIR}/${TARGET}.dylib"
 DYLIB_WORKAROUND = cp "${INSTALLDIR2}/${TARGET}" "${INSTALLDIR2}/${TARGET}.dylib"
else
 DYLIB_WORKAROUND = cp "${INSTALLDIR}/${TARGET}" "${INSTALLDIR}/${TARGET}.so"
 DYLIB_WORKAROUND = cp "${INSTALLDIR2}/${TARGET}" "${INSTALLDIR2}/${TARGET}.so"
 LDFLAGS += -fuse-ld=gold
endif

SRCS = $(wildcard *.c)
OBJS = $(SRCS:.c=.o)

all: $(TARGET)

$(TARGET): $(OBJS)
	$(CC) -shared $(LDFLAGS) -o $@ $^

.PHONY: clean

clean :
	rm -f $(OBJS) $(TARGET)
	rm -rf $(INSTALLDIR)
	rm -rf $(INSTALLDIR2)

.PHONY: install

install:
	mkdir -p $(INSTALLDIR)
	mkdir -p $(INSTALLDIR2)
	install $(TARGET) $(wildcard *.h) $(INSTALLDIR)
	install $(TARGET) $(wildcard *.h) $(INSTALLDIR2)
	$(DYLIB_WORKAROUND)
