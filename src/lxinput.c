/*
 *      lxinput.c
 *
 *      Copyright 2009-2011 PCMan <pcman.tw@gmail.com>
 *      Copyright 2009 martyj19 <martyj19@comcast.net>
 *      Copyright 2011-2013 Julien Lavergne <julien.lavergne@gmail.com>
 *      Copyright 2014 Andriy Grytsenko <andrej@rep.kiev.ua>
 *
 *      This program is free software; you can redistribute it and/or modify
 *      it under the terms of the GNU General Public License as published by
 *      the Free Software Foundation; either version 2 of the License, or
 *      (at your option) any later version.
 *
 *      This program is distributed in the hope that it will be useful,
 *      but WITHOUT ANY WARRANTY; without even the implied warranty of
 *      MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 *      GNU General Public License for more details.
 *
 *      You should have received a copy of the GNU General Public License
 *      along with this program; if not, write to the Free Software
 *      Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston,
 *      MA 02110-1301, USA.
 */

#ifdef HAVE_CONFIG_H
#include <config.h>
#endif

#include <gtk/gtk.h>
#include <glib/gi18n.h>
#include <glib/gstdio.h>
#include <string.h>
#include <math.h>
#include <stdlib.h>
#include <sys/stat.h>
#include <wordexp.h>

#include <gdk/gdkx.h>
#include <X11/Xlib.h>
#include <X11/XKBlib.h>

#define DEFAULT_SES "LXDE-pi"

static char* file = NULL;

static GtkWidget *dlg;
static GtkRange *mouse_accel;
static GtkRange *mouse_threshold;
static GtkRange *mouse_dclick;
static GtkToggleButton* mouse_left_handed;
static GtkRange *kb_delay;
static GtkRange *kb_interval;
static GtkToggleButton* kb_beep;
static GtkButton* kb_layout;
static GtkLabel* kb_layout_label;
static GtkWidget *keymodel_cb, *keylayout_cb, *keyvar_cb;
static GtkWidget *msg_dlg;

static int accel = 20, old_accel = 20;
static int threshold = 10, old_threshold = 10;
static int dclick = 250, old_dclick = 250;
static gboolean left_handed = FALSE, old_left_handed = FALSE;
static float facc = 0.0, old_facc = 0.0;
static char fstr[16];

static int delay = 500, old_delay = 500;
static int interval = 30, old_interval = 30;
static gboolean beep = TRUE, old_beep = TRUE;
static guint dctimer = 0, matimer = 0;

static GList *devs = NULL;

/* Globals accessed from multiple threads */

static char gbuffer[512];
GThread *pthread;

/* Lists for keyboard setting */

GtkListStore *model_list, *layout_list, *variant_list;

char *update_facc_str (void)
{
    char *oldloc = setlocale (LC_NUMERIC, NULL);
    setlocale (LC_NUMERIC, "POSIX");
    sprintf (fstr, "%f", facc);
    setlocale (LC_NUMERIC, oldloc);
    return fstr;
}

float get_float (char *str)
{
    float fval;
    char *oldloc = setlocale (LC_NUMERIC, NULL);
    setlocale (LC_NUMERIC, "POSIX");
    if (sscanf (str, "%f", &fval) != 1) fval = 0;
    setlocale (LC_NUMERIC, oldloc);
    return fval;
}

#if GTK_CHECK_VERSION(3, 0, 0)

/* Client message code copied from GTK+2 */

typedef struct _GdkEventClient GdkEventClient;

struct _GdkEventClient
{
    GdkEventType type;
    GdkWindow *window;
    gint8 send_event;
    GdkAtom message_type;
    gushort data_format;
    union {
        char b[20];
        short s[10];
        long l[5];
    } data;
};

gint _gdk_send_xevent (GdkDisplay *display, Window window, gboolean propagate, glong event_mask, XEvent *event_send)
{
    gboolean result;

    if (gdk_display_is_closed (display)) return FALSE;

    gdk_x11_display_error_trap_push (display);
    result = XSendEvent (GDK_DISPLAY_XDISPLAY (display), window, propagate, event_mask, event_send);
    XSync (GDK_DISPLAY_XDISPLAY (display), False);
    if (gdk_x11_display_error_trap_pop (display)) return FALSE;

    return result;
}

/* Sends a ClientMessage to all toplevel client windows */
static gboolean gdk_event_send_client_message_to_all_recurse (GdkDisplay *display, XEvent *xev, guint32 xid, guint level)
{
    Atom type = None;
    int format;
    unsigned long nitems, after;
    unsigned char *data;
    Window *ret_children, ret_root, ret_parent;
    unsigned int ret_nchildren;
    gboolean send = FALSE;
    gboolean found = FALSE;
    gboolean result = FALSE;
    int i;

    gdk_x11_display_error_trap_push (display);

    if (XGetWindowProperty (GDK_DISPLAY_XDISPLAY (display), xid, 
        gdk_x11_get_xatom_by_name_for_display (display, "WM_STATE"),
        0, 0, False, AnyPropertyType, &type, &format, &nitems, &after, &data) != Success)
            goto out;

    if (type)
    {
        send = TRUE;
        XFree (data);
    }
    else
    {
        /* OK, we're all set, now let's find some windows to send this to */
        if (!XQueryTree (GDK_DISPLAY_XDISPLAY (display), xid, &ret_root, &ret_parent, &ret_children, &ret_nchildren))	
            goto out;

        for (i = 0; i < ret_nchildren; i++)
            if (gdk_event_send_client_message_to_all_recurse (display, xev, ret_children[i], level + 1))
                found = TRUE;

        XFree (ret_children);
    }

    if (send || (!found && (level == 1)))
    {
        xev->xclient.window = xid;
        _gdk_send_xevent (display, xid, False, NoEventMask, xev);
    }

    result = send || found;

    out:
        gdk_x11_display_error_trap_pop (display);

    return result;
}

void gdk_screen_broadcast_client_message (GdkScreen *screen, GdkEventClient *event)
{
    XEvent sev;
    GdkWindow *root_window;

    g_return_if_fail (event != NULL);

    root_window = gdk_screen_get_root_window (screen);

    /* Set up our event to send, with the exception of its target window */
    sev.xclient.type = ClientMessage;
    sev.xclient.display = GDK_WINDOW_XDISPLAY (root_window);
    sev.xclient.format = event->data_format;
    memcpy(&sev.xclient.data, &event->data, sizeof (sev.xclient.data));
    sev.xclient.message_type = gdk_x11_atom_to_xatom_for_display (gdk_screen_get_display (screen), event->message_type);

    gdk_event_send_client_message_to_all_recurse (gdk_screen_get_display (screen), &sev, GDK_WINDOW_XID (root_window), 0);
}

void gdk_event_send_clientmessage_toall (GdkEvent *event)
{
    g_return_if_fail (event != NULL);
    gdk_screen_broadcast_client_message (gdk_screen_get_default (), (GdkEventClient *) event);
}

#endif

static void reload_all_programs (void)
{
    GdkEventClient event;
    event.type = GDK_CLIENT_EVENT;
    event.send_event = TRUE;
    event.window = NULL;
    event.message_type = gdk_atom_intern("_GTK_READ_RCFILES", FALSE);
    event.data_format = 8;
    gdk_event_send_clientmessage_toall((GdkEvent *)&event);
}

static void set_dclick_time (int time)
{
    const char *session_name;
    char *user_config_file, *str, *fname, *scf;
    char cmdbuf[256];
    GKeyFile *kf;
    gsize len;

    // construct the file path
    session_name = g_getenv ("DESKTOP_SESSION");
    if (!session_name) session_name = DEFAULT_SES;
    user_config_file = g_build_filename (g_get_user_config_dir (), "lxsession/", session_name, "/desktop.conf", NULL);

    // read in data from file to a key file
    kf = g_key_file_new ();
    if (!g_key_file_load_from_file (kf, user_config_file, G_KEY_FILE_KEEP_COMMENTS | G_KEY_FILE_KEEP_TRANSLATIONS, NULL))
    {
        // create the local config directory
        scf = g_path_get_dirname (user_config_file);
        g_mkdir_with_parents (scf, 0700);
        g_free (scf);
        // load the global config
        scf = g_build_filename ("/etc/xdg/lxsession/", session_name, "/desktop.conf", NULL);
        g_key_file_load_from_file (kf, scf, G_KEY_FILE_KEEP_COMMENTS | G_KEY_FILE_KEEP_TRANSLATIONS, NULL);
        g_free (scf);
    }

    // update changed values in the key file
    g_key_file_set_integer (kf, "GTK", "iNet/DoubleClickTime", time);

    // write the modified key file out
    str = g_key_file_to_data (kf, &len, NULL);
    g_file_set_contents (user_config_file, str, len, NULL);

    g_free (user_config_file);
    g_free (str);

    reload_all_programs ();
}

static gboolean dclick_handler (gpointer data)
{
    set_dclick_time ((int) data);
    dctimer = 0;
    return FALSE;
}

static void on_mouse_dclick_changed (GtkRange* range, gpointer user_data)
{
    if (dctimer) g_source_remove (dctimer);
    dctimer = g_timeout_add (500, dclick_handler, (gpointer) ((int) gtk_range_get_value (range)));
}

static void set_mouse_accel (void)
{
    char buf[256];
    update_facc_str ();

    GList *l;
    for (l = devs; l != NULL; l = l->next)
    {
        sprintf (buf, "xinput --set-prop %s \"libinput Accel Speed\" %s", l->data, fstr);
        system (buf);
    }

    sprintf (buf, "gsettings set org.gnome.desktop.peripherals.mouse speed %s", fstr);
    system (buf);
}

static gboolean accel_handler (gpointer data)
{
    set_mouse_accel ();
    matimer = 0;
    return FALSE;
}

static void on_mouse_accel_changed (GtkRange* range, gpointer user_data)
{
    if (matimer) g_source_remove (matimer);
    facc = (gtk_range_get_value (range) / 5.0) - 1.0;
    matimer = g_timeout_add (500, accel_handler, NULL);
}

static void on_mouse_threshold_changed(GtkRange* range, gpointer user_data)
{
    /* threshold = 110 - sensitivity. The lower the threshold, the higher the sensitivity */
    threshold = (int)gtk_range_get_value(range);
    XChangePointerControl(GDK_DISPLAY_XDISPLAY(gdk_display_get_default()), False, True,
                             0, 10, threshold);
}

static void set_kbd_rates (void)
{
    char buf[256];

    /* apply keyboard values */
    XkbSetAutoRepeatRate(GDK_DISPLAY_XDISPLAY(gdk_display_get_default()), XkbUseCoreKbd, delay, interval);
    sprintf (buf, "gsettings set org.gnome.desktop.peripherals.keyboard repeat-interval %d", interval);
    system (buf);
    sprintf (buf, "gsettings set org.gnome.desktop.peripherals.keyboard delay %d", delay);
    system (buf);
}

static gboolean kbd_handler (gpointer data)
{
    set_kbd_rates ();
    matimer = 0;
    return FALSE;
}

static void on_kb_range_changed (GtkRange* range, int *val)
{
    if (matimer) g_source_remove (matimer);
    *val = (int) gtk_range_get_value (range);
    matimer = g_timeout_add (500, kbd_handler, NULL);
}

/* This function is taken from Gnome's control-center 2.6.0.3 (gnome-settings-mouse.c) and was modified*/
#define DEFAULT_PTR_MAP_SIZE 128
static void set_left_handed_mouse()
{
    unsigned char *buttons;
    gint n_buttons, i;
    gint idx_1 = 0, idx_3 = 1;

    buttons = g_alloca (DEFAULT_PTR_MAP_SIZE);
    n_buttons = XGetPointerMapping (GDK_DISPLAY_XDISPLAY(gdk_display_get_default()), buttons, DEFAULT_PTR_MAP_SIZE);
    if (n_buttons > DEFAULT_PTR_MAP_SIZE)
    {
        buttons = g_alloca (n_buttons);
        n_buttons = XGetPointerMapping (GDK_DISPLAY_XDISPLAY(gdk_display_get_default()), buttons, n_buttons);
    }

    for (i = 0; i < n_buttons; i++)
    {
        if (buttons[i] == 1)
            idx_1 = i;
        else if (buttons[i] == ((n_buttons < 3) ? 2 : 3))
            idx_3 = i;
    }

    if ((left_handed && idx_1 < idx_3) ||
        (!left_handed && idx_1 > idx_3))
    {
        buttons[idx_1] = ((n_buttons < 3) ? 2 : 3);
        buttons[idx_3] = 1;
        XSetPointerMapping (GDK_DISPLAY_XDISPLAY(gdk_display_get_default()), buttons, n_buttons);
    }
}

static void on_left_handed_toggle(GtkToggleButton* btn, gpointer user_data)
{
    left_handed = gtk_toggle_button_get_active(btn);
    set_left_handed_mouse(left_handed);
}

static void on_kb_beep_toggle(GtkToggleButton* btn, gpointer user_data)
{
    XKeyboardControl values;
    beep = gtk_toggle_button_get_active(btn);
    values.bell_percent = beep ? -1 : 0;
    XChangeKeyboardControl(GDK_DISPLAY_XDISPLAY(gdk_display_get_default()), KBBellPercent, &values);
}

/*
static gboolean on_change_val(GtkRange *range, GtkScrollType scroll,
                                 gdouble value, gpointer user_data)
{
    int interval = GPOINTER_TO_INT(user_data);
    return FALSE;
}
*/

/* Keyboard setting */

static int vsystem (const char *fmt, ...)
{
    char *cmdline;
    int res;

    va_list arg;
    va_start (arg, fmt);
    g_vasprintf (&cmdline, fmt, arg);
    va_end (arg);
    res = system (cmdline);
    g_free (cmdline);
    return res;
}

static char *get_string (char *cmd)
{
    char *line = NULL, *res = NULL;
    size_t len = 0;
    FILE *fp = popen (cmd, "r");

    if (fp == NULL) return NULL;
    if (getline (&line, &len, fp) > 0)
    {
        res = line;
        while (*res)
        {
            if (g_ascii_isspace (*res)) *res = 0;
            res++;
        }
        res = g_strdup (line);
    }
    pclose (fp);
    g_free (line);
    return res;
}

static void set_init (GtkTreeModel *model, GtkWidget *cb, int pos, char *init)
{
    GtkTreeIter iter;
    char *val;

    gtk_tree_model_get_iter_first (model, &iter);
    if (!init) gtk_combo_box_set_active_iter (GTK_COMBO_BOX (cb), &iter);
    else
    {
        while (1)
        {
            gtk_tree_model_get (model, &iter, pos, &val, -1);
            if (!g_strcmp0 (init, val))
            {
                gtk_combo_box_set_active_iter (GTK_COMBO_BOX (cb), &iter);
                g_free (val);
                return;
            }
            g_free (val);
            if (!gtk_tree_model_iter_next (model, &iter)) break;
        }
    }

    // couldn't match - just choose the first option - should never happen, but...
    gtk_tree_model_get_iter_first (model, &iter);
    gtk_combo_box_set_active_iter (GTK_COMBO_BOX (cb), &iter);
}

static void message (char *msg)
{
    GtkWidget *wid;
    GtkBuilder *builder = gtk_builder_new_from_file (PACKAGE_DATA_DIR "/lxinput.ui");

    msg_dlg = (GtkWidget *) gtk_builder_get_object (builder, "modal");
    gtk_window_set_transient_for (GTK_WINDOW (msg_dlg), GTK_WINDOW (dlg));

    wid = (GtkWidget *) gtk_builder_get_object (builder, "modal_msg");
    gtk_label_set_text (GTK_LABEL (wid), msg);

    wid = (GtkWidget *) gtk_builder_get_object (builder, "modal_pb");
    gtk_widget_hide (wid);
    wid = (GtkWidget *) gtk_builder_get_object (builder, "modal_cancel");
    gtk_widget_hide (wid);
    wid = (GtkWidget *) gtk_builder_get_object (builder, "modal_ok");
    gtk_widget_hide (wid);

    gtk_widget_show (msg_dlg);

    g_object_unref (builder);
}

static gboolean close_msg (gpointer data)
{
    gtk_widget_destroy (GTK_WIDGET (msg_dlg));
    return FALSE;
}

static void layout_changed (GtkComboBox *cb, char *init_variant)
{
    FILE *fp;
    GtkTreeIter iter;
    char *buffer, *cptr, *t1, *t2;
    size_t siz;
    int in_list;

    // get the currently-set layout from the combo box
    gtk_combo_box_get_active_iter (GTK_COMBO_BOX (keylayout_cb), &iter);
    gtk_tree_model_get (GTK_TREE_MODEL (layout_list), &iter, 0, &t1, 1, &t2, -1);

    // reset the list of variants and add the layout name as a default
    gtk_list_store_clear (variant_list);
    gtk_list_store_append (variant_list, &iter);
    gtk_list_store_set (variant_list, &iter, 0, t1, 1, "", -1);
    buffer = g_strdup_printf ("    '%s'", t2);
    g_free (t1);
    g_free (t2);

    // parse the database file to find variants for this layout
    cptr = NULL;
    in_list = 0;
    fp = fopen ("/usr/share/console-setup/KeyboardNames.pl", "rb");
    while (getline (&cptr, &siz, fp) > 0)
    {
        if (in_list)
        {
            if (cptr[4] == '}') break;
            else
            {
                strtok (cptr, "'");
                t1 = strtok (NULL, "'");
                strtok (NULL, "'");
                t2 = strtok (NULL, "'");
                strtok (NULL, "'");
                if (in_list == 1)
                {
                    gtk_list_store_append (variant_list, &iter);
                    gtk_list_store_set (variant_list, &iter, 0, t1, 1, t2, -1);
                }
            }
        }
        if (!strncmp (buffer, cptr, strlen (buffer))) in_list = 1;
    }
    fclose (fp);
    g_free (cptr);
    g_free (buffer);

    set_init (GTK_TREE_MODEL (variant_list), keyvar_cb, 1, init_variant);
}

static gpointer keyboard_thread (gpointer ptr)
{
    vsystem ("sudo invoke-rc.d keyboard-setup start");
    vsystem ("sudo setsid sh -c 'exec setupcon -k --force <> /dev/tty1 >&0 2>&1'");
    vsystem ("sudo udevadm trigger --subsystem-match=input --action=change");
    vsystem ("udevadm settle");
    vsystem (gbuffer);
    g_idle_add (close_msg, NULL);
    return NULL;
}

static void read_keyboards (void)
{
    FILE *fp;
    char *cptr, *t1, *t2;
    size_t siz;
    int in_list;
    GtkTreeIter iter;

    // loop through lines in KeyboardNames file
    cptr = NULL;
    in_list = 0;
    fp = fopen ("/usr/share/console-setup/KeyboardNames.pl", "rb");
    while (getline (&cptr, &siz, fp) > 0)
    {
        if (in_list)
        {
            if (cptr[0] == ')') in_list = 0;
            else
            {
                strtok (cptr, "'");
                t1 = strtok (NULL, "'");
                strtok (NULL, "'");
                t2 = strtok (NULL, "'");
                strtok (NULL, "'");
                if (strlen (t1) > 50)
                {
                    t1[47] = '.';
                    t1[48] = '.';
                    t1[49] = '.';
                    t1[50] = 0;
                }
                if (in_list == 1)
                {
                    gtk_list_store_append (model_list, &iter);
                    gtk_list_store_set (model_list, &iter, 0, t1, 1, t2, -1);
                }
                if (in_list == 2)
                {
                    gtk_list_store_append (layout_list, &iter);
                    gtk_list_store_set (layout_list, &iter, 0, t1, 1, t2, -1);
                }
            }
        }
        if (!strncmp ("%models", cptr, 7)) in_list = 1;
        if (!strncmp ("%layouts", cptr, 8)) in_list = 2;
    }
    fclose (fp);
    g_free (cptr);
}

static void on_set_keyboard (GtkButton* btn, gpointer ptr)
{
    FILE *fp;
    GtkBuilder *builder;
    GtkWidget *kdlg;
    GtkCellRenderer *col;
    GtkTreeIter iter;
    char *buffer, *init_model = NULL, *init_layout = NULL, *init_variant = NULL, *new_mod, *new_lay, *new_var;
    int n;

    // set up list stores for keyboard layouts
    model_list = gtk_list_store_new (2, G_TYPE_STRING, G_TYPE_STRING);
    layout_list = gtk_list_store_new (2, G_TYPE_STRING, G_TYPE_STRING);
    variant_list = gtk_list_store_new (2, G_TYPE_STRING, G_TYPE_STRING);
    read_keyboards ();

    // build the dialog and attach the combo boxes
    builder = gtk_builder_new_from_file (PACKAGE_DATA_DIR "/lxinput.ui");
    kdlg = (GtkWidget *) gtk_builder_get_object (builder, "keyboarddlg");
    gtk_window_set_transient_for (GTK_WINDOW (kdlg), GTK_WINDOW (dlg));

    keymodel_cb = (GtkWidget *) gtk_builder_get_object (builder, "keycbmodel");
    keylayout_cb = (GtkWidget *) gtk_builder_get_object (builder, "keycblayout");
    keyvar_cb = (GtkWidget *) gtk_builder_get_object (builder, "keycbvar");
    gtk_combo_box_set_model (GTK_COMBO_BOX (keymodel_cb), GTK_TREE_MODEL (model_list));
    gtk_combo_box_set_model (GTK_COMBO_BOX (keylayout_cb), GTK_TREE_MODEL (layout_list));
    gtk_combo_box_set_model (GTK_COMBO_BOX (keyvar_cb), GTK_TREE_MODEL (variant_list));

    col = gtk_cell_renderer_text_new ();
    gtk_cell_layout_pack_start (GTK_CELL_LAYOUT (keymodel_cb), col, FALSE);
    gtk_cell_layout_add_attribute (GTK_CELL_LAYOUT (keymodel_cb), col, "text", 0);
    gtk_cell_layout_pack_start (GTK_CELL_LAYOUT (keylayout_cb), col, FALSE);
    gtk_cell_layout_add_attribute (GTK_CELL_LAYOUT (keylayout_cb), col, "text", 0);
    gtk_cell_layout_pack_start (GTK_CELL_LAYOUT (keyvar_cb), col, FALSE);
    gtk_cell_layout_add_attribute (GTK_CELL_LAYOUT (keyvar_cb), col, "text", 0);

    // get the current keyboard settings
    init_model = get_string ("grep XKBMODEL /etc/default/keyboard | cut -d = -f 2 | tr -d '\"' | rev | cut -d , -f 1 | rev");
    if (init_model == NULL) init_model = g_strdup ("pc105");

    init_layout = get_string ("grep XKBLAYOUT /etc/default/keyboard | cut -d = -f 2 | tr -d '\"' | rev | cut -d , -f 1 | rev");
    if (init_layout == NULL) init_layout = g_strdup ("gb");

    init_variant = get_string ("grep XKBVARIANT /etc/default/keyboard | cut -d = -f 2 | tr -d '\"' | rev | cut -d , -f 1 | rev");

    set_init (GTK_TREE_MODEL (model_list), keymodel_cb, 1, init_model);
    set_init (GTK_TREE_MODEL (layout_list), keylayout_cb, 1, init_layout);
    g_signal_connect (keylayout_cb, "changed", G_CALLBACK (layout_changed), NULL);
    layout_changed (GTK_COMBO_BOX (keyvar_cb), init_variant);

    g_object_unref (builder);

    // run the dialog
    if (gtk_dialog_run (GTK_DIALOG (kdlg)) == GTK_RESPONSE_OK)
    {
        n = 0;
        gtk_combo_box_get_active_iter (GTK_COMBO_BOX (keymodel_cb), &iter);
        gtk_tree_model_get (GTK_TREE_MODEL (model_list), &iter, 1, &new_mod, -1);
        if (g_strcmp0 (new_mod, init_model))
        {
            vsystem ("grep -q XKBMODEL /etc/default/keyboard && sudo sed -i 's/XKBMODEL=.*/XKBMODEL=%s/g' /etc/default/keyboard || sudo echo 'XKBMODEL=%s' >> /etc/default/keyboard", new_mod, new_mod);
            n = 1;
        }

        gtk_combo_box_get_active_iter (GTK_COMBO_BOX (keylayout_cb), &iter);
        gtk_tree_model_get (GTK_TREE_MODEL (layout_list), &iter, 1, &new_lay, -1);
        if (g_strcmp0 (new_lay, init_layout))
        {
            vsystem ("grep -q XKBLAYOUT /etc/default/keyboard && sudo sed -i 's/XKBLAYOUT=.*/XKBLAYOUT=%s/g' /etc/default/keyboard || sudo echo 'XKBLAYOUT=%s' >> /etc/default/keyboard", new_lay, new_lay);
            n = 1;
        }

        gtk_combo_box_get_active_iter (GTK_COMBO_BOX (keyvar_cb), &iter);
        gtk_tree_model_get (GTK_TREE_MODEL (variant_list), &iter, 1, &new_var, -1);
        if (g_strcmp0 (new_var, init_variant))
        {
            vsystem ("grep -q XKBVARIANT /etc/default/keyboard && sudo sed -i 's/XKBVARIANT=.*/XKBVARIANT=%s/g' /etc/default/keyboard || sudo echo 'XKBVARIANT=%s' >> /etc/default/keyboard", new_var, new_var);
            n = 1;
        }

        // this updates the current session when invoked after the udev update
        sprintf (gbuffer, "setxkbmap %s%s%s%s%s", new_lay, new_mod[0] ? " -model " : "", new_mod, new_var[0] ? " -variant " : "", new_var);
        g_free (new_mod);
        g_free (new_lay);
        g_free (new_var);

        if (n)
        {
            // warn about a short delay...
            message (_("Setting keyboard - please wait..."));

            // launch a thread with the system call to update the keyboard
            pthread = g_thread_new (NULL, keyboard_thread, NULL);
            if (ptr != NULL) gtk_dialog_run (GTK_DIALOG (msg_dlg));
        }
    }

    g_free (init_model);
    g_free (init_layout);
    g_free (init_variant);
    g_object_unref (model_list);
    g_object_unref (layout_list);
    g_object_unref (variant_list);

    gtk_widget_destroy (kdlg);
}

static void set_range_stops(GtkRange* range, int interval )
{
/*
    g_signal_connect(range, "change-value",
                    G_CALLBACK(on_change_val), GINT_TO_POINTER(interval));
*/
}

static void load_settings()
{
    const char* session_name = g_getenv("DESKTOP_SESSION");
	/* load settings from current session config files */
	if (!session_name) session_name = DEFAULT_SES;

    char* rel_path = g_strconcat("lxsession/", session_name, "/desktop.conf", NULL);
    char* user_config_file = g_build_filename(g_get_user_config_dir(), rel_path, NULL);
    GKeyFile* kf = g_key_file_new();

    if(!g_key_file_load_from_file(kf, user_config_file, G_KEY_FILE_KEEP_COMMENTS|G_KEY_FILE_KEEP_TRANSLATIONS, NULL))
    {
        g_key_file_load_from_dirs(kf, rel_path, (const char**)g_get_system_config_dirs(), NULL,
                                  G_KEY_FILE_KEEP_COMMENTS|G_KEY_FILE_KEEP_TRANSLATIONS, NULL);
    }

    g_free(rel_path);

    int val;
    val = g_key_file_get_integer(kf, "Mouse", "AccFactor", NULL);
    if( val > 0)
        old_accel = accel = val;

    val = g_key_file_get_integer(kf, "Mouse", "AccThreshold", NULL);
    if( val > 0)
        old_threshold = threshold = val;

    old_left_handed = left_handed = g_key_file_get_boolean(kf, "Mouse", "LeftHanded", NULL);

    val = g_key_file_get_integer(kf, "Keyboard", "Delay", NULL);
    if(val > 0)
        old_delay = delay = val;
    val = g_key_file_get_integer(kf, "Keyboard", "Interval", NULL);
    if(val > 0)
        old_interval = interval = val;

    if( g_key_file_has_key(kf, "Keyboard", "Beep", NULL ) )
        old_beep = beep = g_key_file_get_boolean(kf, "Keyboard", "Beep", NULL);

    val = g_key_file_get_integer(kf, "GTK", "iNet/DoubleClickTime", NULL);
    if (val > 0)
        old_dclick = dclick = val;

    g_key_file_free(kf);

    g_free(user_config_file);
}

void get_valid_mice (void)
{
    FILE *fp, *fp2;
    char buf[128], *cptr, cmd[256];

    // need to get the device list from xinput first...
    fp = popen ("xinput list | grep pointer | grep slave | cut -f 2 | cut -d = -f 2", "r");
    if (fp == NULL) return;
    while (fgets (buf, sizeof (buf) - 1, fp))
    {
        cptr = buf + strlen (buf) - 1;
        while (*cptr == ' ' || *cptr == '\n') *cptr-- = 0;
        sprintf (cmd, "xinput list-props %s 2>/dev/null | grep -q \"Accel Speed\"", buf);
        fp2 = popen (cmd, "r");
        if (!pclose (fp2)) devs = g_list_append (devs, g_strdup (buf));
    }
    pclose (fp);
}

void read_mouse_speed (void)
{
    FILE *fp;
    char *cmd, buf[20];
    float val;

    if (devs != NULL)
    {
        cmd = g_strdup_printf ("xinput list-props %s | grep \"Accel Speed\" | head -n 1 | cut -f 3", devs->data);
        if (fp = popen (cmd, "r"))
        {
            if (fgets (buf, sizeof (buf) - 1, fp))
            {
                facc = get_float (buf);
                old_facc = facc;
            }
            pclose (fp);
        }
        g_free (cmd);
    }
}

int main(int argc, char** argv)
{
    GtkBuilder* builder;
    char* str = NULL;

    get_valid_mice ();

    GKeyFile* kf = g_key_file_new();
    const char* session_name = g_getenv("DESKTOP_SESSION");
    /* load settings from current session config files */
    if(!session_name)
        session_name = "LXDE";

    char* rel_path = g_strconcat("lxsession/", session_name, "/desktop.conf", NULL);
    char* user_config_file = g_build_filename(g_get_user_config_dir(), rel_path, NULL);

#ifdef ENABLE_NLS
    bindtextdomain ( GETTEXT_PACKAGE, PACKAGE_LOCALE_DIR );
    bind_textdomain_codeset ( GETTEXT_PACKAGE, "UTF-8" );
    textdomain ( GETTEXT_PACKAGE );
#endif

    gtk_init(&argc, &argv);

    gtk_icon_theme_prepend_search_path(gtk_icon_theme_get_default(), PACKAGE_DATA_DIR);

    /* build the UI */
    builder = gtk_builder_new_from_file( PACKAGE_DATA_DIR "/lxinput.ui" );
    dlg = (GtkWidget*)gtk_builder_get_object( builder, "dlg" );
    //gtk_dialog_set_alternative_button_order( (GtkDialog*)dlg, GTK_RESPONSE_OK, GTK_RESPONSE_CANCEL, -1 );

    mouse_accel = (GtkRange*)gtk_builder_get_object(builder,"mouse_accel");
    //mouse_threshold = (GtkRange*)gtk_builder_get_object(builder,"mouse_threshold");
    mouse_left_handed = (GtkToggleButton*)gtk_builder_get_object(builder,"left_handed");
    mouse_dclick = (GtkRange*)gtk_builder_get_object(builder, "mouse_dclick");

    kb_delay = (GtkRange*)gtk_builder_get_object(builder,"kb_delay");
    kb_interval = (GtkRange*)gtk_builder_get_object(builder,"kb_interval");
    kb_beep = (GtkToggleButton*)gtk_builder_get_object(builder,"beep");
    kb_layout = (GtkButton*)gtk_builder_get_object(builder,"keyboard_layout");

    gtk_button_set_label(kb_layout, _("Keyboard Layout..."));

    g_object_unref( builder );


    /* read the config file */
    load_settings();
    read_mouse_speed ();
    update_facc_str ();

    /* init the UI */
    gtk_range_set_value(mouse_accel, (facc + 1) * 5.0);
    //gtk_range_set_value(mouse_threshold, threshold);
    gtk_range_set_value(mouse_dclick, dclick);
    gtk_toggle_button_set_active(mouse_left_handed, left_handed);

    gtk_range_set_value(kb_delay, delay);
    gtk_range_set_value(kb_interval, interval);
    gtk_toggle_button_set_active(kb_beep, beep);

    set_range_stops(mouse_accel, 10);
    g_signal_connect(mouse_accel, "value-changed", G_CALLBACK(on_mouse_accel_changed), NULL);
    //set_range_stops(mouse_threshold, 10);
    //g_signal_connect(mouse_threshold, "value-changed", G_CALLBACK(on_mouse_threshold_changed), NULL);
    g_signal_connect(mouse_left_handed, "toggled", G_CALLBACK(on_left_handed_toggle), NULL);
    g_signal_connect(mouse_dclick, "value-changed", G_CALLBACK(on_mouse_dclick_changed), NULL);

    set_range_stops(kb_delay, 10);
    g_signal_connect(kb_delay, "value-changed", G_CALLBACK(on_kb_range_changed), &delay);
    set_range_stops(kb_interval, 10);
    g_signal_connect(kb_interval, "value-changed", G_CALLBACK(on_kb_range_changed), &interval);
    g_signal_connect(kb_beep, "toggled", G_CALLBACK(on_kb_beep_toggle), NULL);
    g_signal_connect(kb_layout, "clicked", G_CALLBACK(on_set_keyboard), NULL);

    if( gtk_dialog_run( (GtkDialog*)dlg ) == GTK_RESPONSE_OK )
    {
        gsize len;

        if(!g_key_file_load_from_file(kf, user_config_file, G_KEY_FILE_KEEP_COMMENTS|G_KEY_FILE_KEEP_TRANSLATIONS, NULL))
        {
            /* the user config file doesn't exist, create its parent dir */
            len = strlen(user_config_file) - strlen("/desktop.conf");
            user_config_file[len] = '\0';
            g_debug("user_config_file = %s", user_config_file);
            g_mkdir_with_parents(user_config_file, 0700);
            user_config_file[len] = '/';

            g_key_file_load_from_dirs(kf, rel_path, (const char**)g_get_system_config_dirs(), NULL,
                                      G_KEY_FILE_KEEP_COMMENTS|G_KEY_FILE_KEEP_TRANSLATIONS, NULL);
        }

        g_free(rel_path);

        g_key_file_set_integer(kf, "Mouse", "AccFactor", accel);
        g_key_file_set_integer(kf, "Mouse", "AccThreshold", threshold);
        g_key_file_set_integer(kf, "Mouse", "LeftHanded", !!left_handed);

        g_key_file_set_integer(kf, "Keyboard", "Delay", delay);
        g_key_file_set_integer(kf, "Keyboard", "Interval", interval);
        g_key_file_set_integer(kf, "Keyboard", "Beep", !!beep);

        str = g_key_file_to_data(kf, &len, NULL);
        g_file_set_contents(user_config_file, str, len, NULL);
        g_free(str);

        /* ask the settigns daemon to reload */
        /* FIXME: is this needed? */
        /* g_spawn_command_line_sync("lxde-settings-daemon reload", NULL, NULL, NULL, NULL); */

        /* also save settings into autostart file for non-lxsession sessions */
        g_free(user_config_file);
        rel_path = g_build_filename(g_get_user_config_dir(), "autostart", NULL);
        user_config_file = g_build_filename(rel_path, "LXinput-setup.desktop", NULL);
        if (g_mkdir_with_parents(rel_path, 0755) == 0)
        {
            str = g_strdup_printf("[Desktop Entry]\n"
                                  "Type=Application\n"
                                  "Name=%s\n"
                                  "Comment=%s\n"
                                  "NoDisplay=true\n"
                                  "Exec=sh -c 'xset m %d/10 %d r rate %d %d b %s%s; for id in $(xinput list | grep pointer | grep slave | cut -f 2 | cut -d = -f 2 ) ; do xinput --set-prop $id \"libinput Accel Speed\" %s 2> /dev/null ; done'\n"
                                  "NotShowIn=GNOME;KDE;XFCE;\n",
                                  _("LXInput autostart"),
                                  _("Setup keyboard and mouse using settings done in LXInput"),
                                  /* FIXME: how to setup left-handed mouse? */
                                  accel, threshold, delay, 1000 / interval,
                                  beep ? "on" : "off",
                                  left_handed ? ";xmodmap -e \"pointer = 3 2 1\"" : "",
                                  fstr);
            g_file_set_contents(user_config_file, str, -1, NULL);
            g_free(str);
        }
    }
    else
    {
        /* restore to original settings */

        /* keyboard */
        delay = old_delay;
        interval = old_interval;
        beep = old_beep;
        XkbSetAutoRepeatRate(GDK_DISPLAY_XDISPLAY(gdk_display_get_default()), XkbUseCoreKbd, delay, interval);
        /* FIXME: beep? */

        /* mouse */
        accel = old_accel;
        threshold = old_threshold;
        left_handed = old_left_handed;
        //XChangePointerControl(GDK_DISPLAY_XDISPLAY(gdk_display_get_default()), True, True,
        //                         accel, 10, threshold);
        set_left_handed_mouse();
        set_dclick_time (old_dclick);

        char buf[256];
        facc = old_facc;
        update_facc_str ();
        GList *l;
        for (l = devs; l != NULL; l = l->next)
        {
            sprintf (buf, "xinput --set-prop %s \"libinput Accel Speed\" %s", l->data, fstr);
            system (buf);
        }
    }

    gtk_widget_destroy( dlg );

	g_free( file );
    g_key_file_free( kf );
    g_free(user_config_file);

    return 0;
}
