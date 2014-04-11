#! /usr/bin/env python3

from argparse import ArgumentParser, REMAINDER, ArgumentDefaultsHelpFormatter
import os
import sys

class CmpSMTException (Exception):
    def __init__ (self, msg):
        self.msg = msg
    def __str__ (self):
        return "[cmpsmt] Error: {0:s}".format(self.msg)

# required for loading additional resources for --html
SCRIPTDIR = os.path.dirname(os.path.realpath(__file__))

g_args = None
g_benchmarks = []

COLOR_BEST = '\033[36m'
COLOR_DIFF = '\033[32m'
COLOR_DISC = '\033[31m'
COLOR_STAT = '\033[33m'
COLOR_NOCOLOR = '\033[0m'

HTML_CLASS = {
    COLOR_BEST: 'best',
    COLOR_DIFF: 'diff',
    COLOR_DISC: 'disc',
    COLOR_STAT: 'stat'
}

def _get_name_and_ext (filename):
    return ("".join(filename.rpartition('.')[:-2]), filename.rpartition('.')[-1])


# per directory/file flag
# column_name : <colname>, <keyword>, <filter>, <is_dir_stat>
FILTER_LOG = {
  'lods':       ['LODS', b'LOD', lambda x: int(x.split()[3]), False],
  'calls':      ['CALLS', b'SAT calls', lambda x: int(x.split()[1]), False],
  'time_sat':   ['SAT[s]', b'pure SAT', lambda x: float(x.split()[1]), False],
  'time_rw':    ['RW[s]', b'rewriting engine', lambda x: float(x.split()[1]),
                 False],
  'time_beta':  ['BETA[s]', b'beta-reduction', lambda x: float(x.split()[1]),
                 False],
  'time_eval':  ['EVAL[s]', b'seconds expression evaluation',
                 lambda x: float(x.split()[1]), False]
}

def err_extract_status(line):
    status = line.split()[2:]
    if b'ok' == status[0]:
        return "ok"
    elif b'time' == status[-1]:
        return "time"
    elif b'memory' == status[-1]:
        return "mem"
    else:
        raise CmpSMTException("invalid status")

def err_extract_opts(line):
    opt = str(line.split()[2])
    if opt[2] == '-':
        return opt[2:-1]
    return None 

# column_name : <colname>, <keyword>, <filter>, [<is_dir_stat>] (optional)
FILTER_ERR = {
  'status':      ['STAT', b'status:', err_extract_status, False],
  'result':      ['RES', b'result:', lambda x: int(x.split()[2]), False],
  'time_real':   ['REAL[s]', b'real:', lambda x: float(x.split()[2]), False],
  'time_time':   ['TIME[s]', b'time:', lambda x: float(x.split()[2]), False],
  'space':       ['SPACE[MB]', b'space:', lambda x: float(x.split()[2]), False],
  'opts':        ['OPTIONS', b'argv', err_extract_opts, True] 
}

assert(set(FILTER_LOG.keys()).isdisjoint(set(FILTER_ERR.keys())))

FILE_STATS_KEYS = list(k for k, f in FILTER_LOG.items() if not f[3])
FILE_STATS_KEYS.extend(list(k for k, f in FILTER_ERR.items() if not f[3]))

DIR_STATS_KEYS = list(k for k, f in FILTER_LOG.items() if f[3])
DIR_STATS_KEYS.extend(list(k for k, f in FILTER_ERR.items() if f[3]))

g_dir_stats = dict((k, {}) for k in DIR_STATS_KEYS)
g_file_stats = dict((k, {}) for k in FILE_STATS_KEYS)
g_best_stats = dict((k, {}) for k in FILE_STATS_KEYS)
g_diff_stats = dict((k, {}) for k in FILE_STATS_KEYS)

g_dir_stats_init = dict((k, False) for k in DIR_STATS_KEYS)

def _filter_data(d, file, filters):
    global g_file_stats, g_dir_stats_init

    with open(os.path.join(d, file), 'rb') as infile:
        f_name = _get_name_and_ext(file)[0]

        dir_stats_tmp = dict((k, []) for k in DIR_STATS_KEYS) 
        for line in infile:
            for k, f in filters.items():
                val = f[2](line) if f[1] in line else None
                
                if k in DIR_STATS_KEYS:
                    if d in g_dir_stats:
                        continue

                    if val is not None:
                        dir_stats_tmp[k].append(val)
                else:
                    assert(k in FILE_STATS_KEYS)
                    if d not in g_file_stats[k]:
                        g_file_stats[k][d] = {}

                    if f_name not in g_file_stats[k][d]:
                        g_file_stats[k][d][f_name] = None

                    if val is not None:
                        g_file_stats[k][d][f_name] = val

        for k, vals in dir_stats_tmp.items():
            g_dir_stats[k][d] = vals


def _read_log_file(d, f):
    _filter_data(d, f, FILTER_LOG)


def _read_err_file(d, f):
    global g_file_stats

    try:
        _filter_data(d, f, FILTER_ERR)
    
        # TODO: move to normalize method or something like that
        # update status for errors ('err' instead of 'ok')
        f_name = _get_name_and_ext(f)[0]
        if g_file_stats['status'][d][f_name] == "ok" \
           and g_file_stats['result'][d][f_name] not in (10, 20):
            g_file_stats['status'][d][f_name] = "err"
    except CmpSMTException as e:
        raise CmpSMTException("{} in file {}".format(str(e), f))


def _read_data (dirs):
    for d in dirs:
        for f in os.listdir(d):
            (f_name, f_ext) = _get_name_and_ext (f)
            if f_ext == "log":
                f_full_log = os.path.join(d, f)
                if os.path.isfile(f_full_log):
                    f_full_err = "{}{}".format(f_full_log[:-3], "err")
                    if not os.path.exists(f_full_err):
                        raise CmpSMTException (
                                "missing matching .err file for '{}'".format(
                                    "{}{}".format(f_full_log)))
                    # init data
                    if not g_args.filter or g_args.filter in str(f):
                        if f_name not in g_benchmarks:
                            g_benchmarks.append(f_name)
                        _read_log_file (d, f)
                        _read_err_file (d, "{}{}".format(f[:-3], "err"))


def _pick_data():
    global g_file_stats, g_best_stats, g_diff_stats

    for f in g_benchmarks:
        for k in g_file_stats.keys():
            v = sorted([(g_file_stats[k][d][f], d) for d in g_args.dirs])

            # strings are not considered for diff/best values
            if isinstance(v[0][0], str):
                g_best_stats[k][f] = None
                g_diff_stats[k][f] = None
                continue

            g_best_stats[k][f] = None \
                if len(set([t[0] for t in v])) <= 1 \
                   or g_file_stats['status'][d][f] != 'ok' else v[0][1]

            g_diff_stats[k][f] = None \
                if g_best_stats[k][f] is None \
                   or v[0][0] * (1 + g_args.diff) > v[1][0] \
                else v[0][1]


def _format_field(field, width, color=None, colspan=0, classes=[]):
    field = "-" if field is None else str(field)

    if g_args.html:
        tag = "td"
        if color is not None and color != COLOR_NOCOLOR:
            classes.append(HTML_CLASS[color])
        if "header" in classes:
            tag = "th"
            classes = classes[:]
            classes.remove("header")
        c = ' class="{}"'.format(" ".join(classes)) if len(classes) > 0 else ''
        colspan = ' colspan="{}"'.format(colspan) if colspan > 0 else ''
        field = "<{0:s}{1:s}{2:s}>{3:s}</{0:s}>".format(tag, c, colspan, field)
    else:
        field = field.rjust(width)
        if color:
            field = "{}{}{}".format(color, field, COLOR_NOCOLOR)

    return field


def _print_row (columns, widths, colors=None, colspans=None, classes=[]):
    assert(len(columns) == len(widths))

    formatted_cols = []
    for i in range(len(columns)):
        column = columns[i]
        width = widths[i]
        color = None if colors is None else colors[i]
        colspan = 0 if colspans is None else colspans[i]
        clazzes = [] if len(classes) == 0 else classes[i]
        if isinstance(column, list):
            assert(isinstance(width, list))
            assert(isinstance(clazzes, list))
            cols = []
            for j in range(len(column)):
                clz = [] if len(clazzes) == 0 else clazzes[j]
                cols.append(_format_field(column[j], width[j], color,
                                          colspan=colspan, classes=clz))
            column = "".join(cols)
        else:
            column = _format_field(column, width, color, colspan, clazzes)

        formatted_cols.append(column)

    if g_args.html:
        print("<tr>{}</tr>".format("".join(formatted_cols)))
    else:
        print("{} |".format(" | ".join(formatted_cols)))


def _print_html_header():

    style_css = ""
    with open("{}/html/style.css".format(SCRIPTDIR), "r") as f:
        style_css = f.read().replace('\n', '')

    jquery_js = ""
    with open("{}/html/jquery.js".format(SCRIPTDIR), "r") as f:
        jquery_js = f.read().replace('\n', '') 

    tableheaders_js = ""
    with open("{}/html/stickytableheaders.js".format(SCRIPTDIR), "r") as f:
        tableheaders_js = f.read().replace('\n', '') 

    print("""<html>
               <head>
                 <style>{}</style>
                 <script type="text/javascript">{}</script>
                 <script type="text/javascript">{}</script>
                 <script type="text/javascript">
                    $(function() {{ $("#results").stickyTableHeaders(); }});
                 </script>
               </head>
               <body>""".format(style_css, jquery_js, tableheaders_js))
    print("""    <table id="legend">
                   <tr>
                     <th>LEGEND</th>
                     <td class="best">best value</td>
                     <td class="diff">difference of '{}' >= {}</td>
                     <td class="disc">discrepancy</td>
                     <td class="stat">status differs</td>
                   </tr>
                 </table>
                 <table id="results">
                    <thead>""".format(g_args.cmp_col, g_args.diff))

def _print_html_footer():
    print("<tbody></table></body></html>")

def _has_status(status, f):
    return status in set(g_file_stats['status'][d][f] for d in g_args.dirs)

def _get_column_name(key):
    if key in FILTER_LOG:
        return FILTER_LOG[key][0]
    assert(key in FILTER_ERR)
    return FILTER_ERR[key][0]

def _get_color(f, d):
    global g_diff_stats, g_best_stats

    for k in g_diff_stats.keys():
        if g_args.cmp_col == k:
            if g_diff_stats[k][f] == d:
                return COLOR_DIFF
            elif g_best_stats[k][f] == d:
                return COLOR_BEST

    return COLOR_NOCOLOR


def _print_data ():
    global g_file_stats, g_dir_stats

    padding = 1
    benchmark_column_width = padding + max(len(b) for b in g_benchmarks) 

    column_groups = {}
    for d in g_args.dirs:
        column_groups[d] = list(g_args.columns)

    data_column_widths = dict((k, {}) for k in g_file_stats.keys())
    for d in g_args.dirs:
        for k in g_file_stats.keys():
            data_column_widths[k][d] = \
                padding + \
                max(len(_get_column_name(k)),
                    max(len(str(val)) for val in g_file_stats[k][d].values()))

    header_column_widths = {} 
    for d, g in column_groups.items():
        width = 0
        for k in g:
            width += data_column_widths[k][d]
        header_column_widths[d] = width

    if g_args.html:
        _print_html_header()
    
    columns = ["DIRECTORY"]
    columns.extend([os.path.basename(d.rstrip('/')) for d in g_args.dirs])
    widths = [benchmark_column_width]
    widths.extend([max(header_column_widths[d], len(d)) for d in g_args.dirs])
    colspans = [0]
    colspans.extend([len(g) for g in column_groups.values()])

    classes = [["header"]]
    classes.extend([["borderleft", "header"] for d in g_args.dirs])
    _print_row (columns, widths, colspans=colspans, classes=classes)

    for k in g_dir_stats:
        columns = [_get_column_name(k)]
        for d in g_args.dirs:
            columns.append(" ".join(g_dir_stats[k][d]))
        _print_row (columns, widths, colspans=colspans, classes=classes)

    columns = ["BENCHMARK"]
    widths = [benchmark_column_width]
    classes = [["header"]]

    for d in g_args.dirs:
        classes.append([["header"] for k in g_args.columns])
        classes[-1][0].append("borderleft")
        columns.append([_get_column_name(k) for k in g_args.columns])
        widths.append([data_column_widths[k][d] for k in g_args.columns])
    _print_row (columns, widths, classes=classes)

    if g_args.html:
        print("</thead><tbody>")

    # print data rows
    for f in sorted(g_benchmarks, key=lambda s: s.lower()):
        if g_args.t and not _has_status('time', f):
            continue
        if g_args.e and not _has_status('err', f):
            continue
        if g_args.o and not _has_status('ok', f):
            continue

        s = [g_file_stats['status'][d][f] for d in g_args.dirs]
        r = [g_file_stats['result'][d][f] for d in g_args.dirs]

        # row color
        color = COLOR_STAT \
                if len(set(s)) > 1 \
                else (COLOR_DISC if len(set(r)) > 1 else COLOR_NOCOLOR)

        columns = [f]
        widths = [benchmark_column_width]
        colors = [color]
        classes = [["nowrap"]]

        for d in g_args.dirs:
            classes.append([["borderleft"]])
            classes[-1].extend([[] for i in range(len(g_args.columns) - 1)])
            columns.append([g_file_stats[k][d][f] for k in g_args.columns])
            widths.append([data_column_widths[k][d] for k in g_args.columns])
            colors.append(color if color != COLOR_NOCOLOR else _get_color(f, d))

        _print_row(columns, widths, colors=colors, classes=classes)

    if g_args.html:
        _print_html_footer()


if __name__ == "__main__":
    try:
        aparser = ArgumentParser(
                      formatter_class=ArgumentDefaultsHelpFormatter,
                      epilog="availabe values for column: {{{}}}".format(", ".join(sorted(FILE_STATS_KEYS))))
        aparser.add_argument ("-f", metavar="string", dest="filter", type=str, 
                default=None,
                help="filter benchmark files by <string>")
        aparser.add_argument ("-d", metavar="float", dest="diff", type=float,
                default=0.1,
                help="highlight difference if greater than <float>")
        aparser.add_argument ("-t", action="store_true",
                help="show timeouts only")
        aparser.add_argument ("-m", action="store_true",
                help="show memory outs only")
        aparser.add_argument ("-e", action="store_true",
                help="show errors only")
        aparser.add_argument ("-o", action="store_true",
                help="show non-errors only")
        aparser.add_argument ("-c", metavar="column", dest="cmp_col", 
                default='time_time',
                choices=FILE_STATS_KEYS,
                help="compare results column")
        aparser.add_argument ("-s", metavar="column[,column ...]",
                dest="columns",
                default="status,result,time_real,time_time,space",
                help="list of columns to print")
        aparser.add_argument ("-a", dest="show_all", action="store_true",
                help="print all columns")
        aparser.add_argument ("--html", action="store_true",
                help="generte html output")
        aparser.add_argument ("dirs", nargs=REMAINDER,
                help="two or more smt run directories to compare")
        g_args = aparser.parse_args()

        if len(g_args.dirs) < 2:
            raise CmpSMTException ("invalid number of dirs given")

        for d in g_args.dirs:
            if not os.path.isdir(d):
                raise CmpSMTException ("given smt run is not a directory")

        g_args.columns = g_args.columns.split(',')
        for c in g_args.columns:
            if c not in FILE_STATS_KEYS:
                raise CmpSMTException("column '{}' not available".format(c))

        if g_args.show_all:
            g_args.columns = FILE_STATS_KEYS

        _read_data (g_args.dirs)
        _pick_data ()
        _print_data ()

    except KeyboardInterrupt as e:
        sys.exit ("[cmpsmt] interrupted")
    except CmpSMTException as e:
        sys.exit (str(e))

