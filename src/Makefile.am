AM_CPPFLAGS = \
	-DPACKAGE_DATA_DIR=\""$(datadir)"/lxinput\" \
	-DPACKAGE_LOCALE_DIR=\""$(prefix)/$(DATADIRNAME)/locale"\" \
	$(GTK_CFLAGS) \
	$(XLIB_CFLAGS) \
    $(ADDITIONAL_FLAGS) \
	-Werror-implicit-function-declaration

bin_PROGRAMS = lxinput

lxinput_SOURCES = \
	lxinput.c

lxinput_LDADD = \
	$(GTK_LIBS) \
	$(XLIB_LIBS) \
	$(INTLLIBS)
