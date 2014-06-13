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
  'lods':       ['LODS', 
                 lambda x: b'LOD' in x, 
                 lambda x: int(x.split()[3]), 
                 False],
  'lods_avg':   ['LODS avg',
                 lambda x: b'average lemma size' in x,
                 lambda x: float(x.split()[4]),
                 False],
  'lods_fc':   ['LODS FC',
                 lambda x: b'function congruence conf' in x,
                 lambda x: int(x.split()[4]),
                 False],
  'lods_br':   ['LODS BR',
                 lambda x: b'beta reduction conf' in x,
                 lambda x: int(x.split()[4]),
                 False],
  'calls':      ['CALLS', 
                 lambda x: b'SAT calls' in x, 
                 lambda x: int(x.split()[1]), 
                 False],
  'time_sat':   ['SAT[s]', 
                 lambda x: b'pure SAT' in x, 
                 lambda x: float(x.split()[1]), 
                 False],
  'time_rw':    ['RW[s]', 
                 lambda x: b'rewriting engine' in x, 
                 lambda x: float(x.split()[1]),
                 False],
  'time_beta':  ['BETA[s]', 
                 lambda x: b'beta-reduction' in x, 
                 lambda x: float(x.split()[1]),
                 False],
  'time_eval':  ['EVAL[s]', 
                 lambda x: b'seconds expression evaluation' in x,
                 lambda x: float(x.split()[1]), 
                 False],
  'time_lle':   ['LLE[s]', 
                 lambda x: b'lazy lambda encoding' in x,
                 lambda x: float(x.split()[1]), 
                 False],
  'time_pas':   ['PAS[s]', 
                 lambda x: b'propagation apply search' in x,
                 lambda x: float(x.split()[1]), 
                 False],
  'time_pacs':   ['PAS[s]',
                 lambda x: b'propagation apply in conds search' in x,
                 lambda x: float(x.split()[1]),
                 False],
  'time_neas':  ['NEAS[s]', 
                 lambda x: b'not encoded apply search' in x,
                 lambda x: float(x.split()[1]), 
                 False],
  'num_beta':   ['BETA', 
                 lambda x: b'beta reductions:' in x,
                 lambda x: int(x.split()[3]), 
                 False],
  'num_eval':   ['EVAL', 
                 lambda x: b'evaluations:' in x,
                 lambda x: int(x.split()[3]), 
                 False],
  'num_prop':   ['PROP', 
                 lambda x: b'propagations:' in x,
                 lambda x: int(x.split()[2]), 
                 False],
  'num_propd':   ['PROPD', 
                  lambda x: b'propagations down:' in x,
                  lambda x: int(x.split()[3]), 
                  False],
  'time_clapp': ['CLONE[s]', 
                 lambda x: b'cloning for initial applies search' in x,
                 lambda x: float(x.split()[1]), 
                 False],
  'time_sapp':  ['SATDP[s]', 
                 lambda x: b'SAT solving for initial applies search' in x,
                 lambda x: float(x.split()[1]), 
                 False],
  'time_app':   ['APP[s]', 
                 lambda x: b'seconds initial applies search' in x,
                 lambda x: float(x.split()[1]), 
                 False],
  'time_coll':  ['COL[s]', 
                 lambda x: b'collecting initial applies' in x, 
                 lambda x: float(x.split()[1]), 
                 False],
  'num_fvars':  ['FVAR',
          lambda x: b'dual prop: failed vars:' in x,
                 lambda x: int(x.split()[5]),
                 False],
  'num_fapps':  ['FAPP',
                 lambda x: b'dual prop: failed applies:' in x,
                 lambda x: int(x.split()[5]),
                 False]
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
  'status':    ['STAT', 
                lambda x: b'status:' in x, err_extract_status, False],
  'result':    ['RES', 
                lambda x: b'result:' in x, lambda x: int(x.split()[2]), False],
  'time_real': ['REAL[s]', 
                lambda x: b'real:' in x, lambda x: float(x.split()[2]), False],
  'time_time': ['TIME[s]', 
                lambda x: b'time:' in x, lambda x: float(x.split()[2]), False],
  'space':     ['SPACE[MB]', 
                lambda x: b'space:' in x, lambda x: float(x.split()[2]), False],
  'opts':      ['OPTIONS', 
                lambda x: b'argv' in x, err_extract_opts, True] 
}


# column_name : <colname>, <keyword>, <filter>, [<is_dir_stat>] (optional)
FILTER_OUT = {
  'models_arr':  ['MARR', lambda x: b'[' in x, lambda x: 1, False],
  'models_bvar': ['MVAR', lambda x: b'[' not in x, lambda x: 1, False]
}

TOTALS_OP = {
  'status':    lambda l: '{}/{}'.format(l.count('ok'), len(l)),
  'result':    lambda l: '{}/{}'.format(l.count(10), l.count(20)),
  'time_time': lambda l: round(sum(l), 2),
  'num_prop':  lambda l: sum(l),
  'num_propd': lambda l: sum(l),
  'lods':      lambda l: sum(l),
  'lods_br':   lambda l: sum(l),
  'lods_fc':   lambda l: sum(l),
  'lods_avg':  lambda l: round(sum(l)/len(l), 2),
  'time_sat':  lambda l: round(sum(l), 2),
  'time_sapp': lambda l: round(sum(l), 2),
}

assert(set(FILTER_LOG.keys()).isdisjoint(set(FILTER_ERR.keys())))
assert(set(FILTER_LOG.keys()).isdisjoint(set(FILTER_OUT.keys())))
assert(set(FILTER_ERR.keys()).isdisjoint(set(FILTER_OUT.keys())))

FILE_STATS_KEYS = list(k for k, f in FILTER_LOG.items() if not f[3])
FILE_STATS_KEYS.extend(list(k for k, f in FILTER_ERR.items() if not f[3]))
FILE_STATS_KEYS.extend(list(k for k, f in FILTER_OUT.items() if not f[3]))

DIR_STATS_KEYS = list(k for k, f in FILTER_LOG.items() if f[3])
DIR_STATS_KEYS.extend(list(k for k, f in FILTER_ERR.items() if f[3]))

g_dir_stats = dict((k, {}) for k in DIR_STATS_KEYS)
g_file_stats = dict((k, {}) for k in FILE_STATS_KEYS)
g_best_stats = dict((k, {}) for k in FILE_STATS_KEYS)
g_diff_stats = dict((k, {}) for k in FILE_STATS_KEYS)
g_total_stats = dict((k, {}) for k in FILE_STATS_KEYS)



def _filter_data(d, file, filters):
    global g_file_stats
    
    with open(os.path.join(d, file), 'rb') as infile:
        (f_name, f_ext) = _get_name_and_ext(file)
        dir_stats_tmp = dict((k, []) for k in DIR_STATS_KEYS) 

        if os.stat(os.path.join(d, file)).st_size == 0:
            for k in filters:
                if d not in g_file_stats[k]:
                    g_file_stats[k][d] = {}
                if f_name not in g_file_stats[k][d]:
                    g_file_stats[k][d][f_name] = None
            return
        
        for line in infile:
            line = line.strip()

            for k, v in filters.items():
                assert(len(v) == 4)
                val = v[2](line) if v[1](line) else None
                
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

                    if f_ext == 'out' \
                       and line in (b'sat', b'unsat', b'unknown'): 
                           continue
            
                    if val is not None:
                        if g_file_stats[k][d][f_name] == None:
                            g_file_stats[k][d][f_name] = val
                        else:
                            g_file_stats[k][d][f_name] += val

        for k,v in dir_stats_tmp.items():
            if d in g_dir_stats[k]:
                continue
            g_dir_stats[k][d] = v


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


def _read_out_file(d, f):
    _filter_data(d, f, FILTER_OUT)


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
                        _read_err_file (d, "{}{}".format(f[:-3], "err"))
                        _read_log_file (d, f)
                        if g_args.m:
                            outfile = "{}{}".format(f[:-3], "out")
                            if not os.path.isfile(os.path.join (d, outfile)):
                                raise CmpSMTException ("missing '{}'".format (
                                    os.path.join (d, outfile)))
                            _read_out_file (d, "{}{}".format(f[:-3], "out"))


def _pick_data():
    global g_file_stats, g_best_stats, g_diff_stats

    for f in g_benchmarks:
        for k in g_file_stats.keys():
            for d in g_args.dirs:
                if f not in g_file_stats[k][d]:
                    g_file_stats[k][d][f] = None
            v = sorted([(g_file_stats[k][d][f], d) for d in g_args.dirs \
                    if g_file_stats[k][d][f] is not None])
            # strings are not considered for diff/best values
            if len(v) == 0 or isinstance(v[0][0], str):
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


def _compute_totals():
    for k in g_file_stats.keys():
        for d in g_file_stats[k].keys():
            g_total_stats[k][d] = \
                [v for v in g_file_stats[k][d].values() if v is not None]


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

def _print_result_table():
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
    elif key in FILTER_ERR:
        return FILTER_ERR[key][0]
    assert(key in FILTER_OUT)
    return FILTER_OUT[key][0]


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
        print("<table><thead>")

    if g_args.html:
        print("</thead><tbody>")
        # print totals
        columns = ["DIRECTORY"]
        columns.append([_get_column_name(k) for k in g_args.columns])
        widths = [benchmark_column_width]
        widths.append([data_column_widths[k][d] for k in g_args.columns])
        classes = [["header"]]
        classes.append([["header"] for k in g_args.columns])
        _print_row (columns, widths, classes=classes)

        for d in g_args.dirs:
            columns = ([os.path.basename(d.rstrip('/'))])
            cols = []
            for k in g_args.columns:
                if k in TOTALS_OP:
                    cols.append(TOTALS_OP[k](g_total_stats[k][d]))
                else:
                    cols.append('-')
            columns.append(cols)
            classes = [["nowrap"]]
            classes.append([[] for k in g_args.columns])
            _print_row (columns, widths, classes=classes)

    if g_args.html:
        print("</tbody></table><br/><br/>")
        _print_result_table()
    
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
        if g_args.time and not _has_status('time', f):
            continue
        if g_args.err and not _has_status('err', f):
            continue
        if g_args.ok and not _has_status('ok', f):
            continue
        if g_args.mem and not _has_status('mem', f):
            continue

        s = [g_file_stats['status'][d][f] for d in g_args.dirs
                if g_file_stats['status'][d][f]]
        r = [g_file_stats['result'][d][f] for d in g_args.dirs
                if g_file_stats['result'][d][f]]

        if g_args.dis:
            r_tmp = [x for x in r if x == 10 or x == 20]
            if not len(set(r_tmp)) > 1: continue

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
                      epilog="availabe values for column: {{ {} }}, " \
                             "note: {{ {} }} are enabled for '-M' only.".format(
                          ", ".join(sorted(FILE_STATS_KEYS)),
                          ", ".join(sorted(list(FILTER_OUT.keys())))))
        aparser.add_argument ("-f", metavar="string", dest="filter", type=str, 
                default=None,
            help="filter benchmark files by <string>")
        aparser.add_argument ("-hd", metavar="float", dest="diff", type=float,
                default=0.1,
                help="highlight difference if greater than <float>")
        aparser.add_argument ("-bs", action="store_true",
                help="compare boolector statistics")
        aparser.add_argument ("-dp", action="store_true",
                help = "compare dual prop statistics")
        aparser.add_argument ("-m", action="store_true",
                help="extract models statistics")
        aparser.add_argument ("-M", action="store_true",
                help="compare models statistics")
        aparser.add_argument ("-dis", action="store_true",
                help="show discrepancies only")
        aparser.add_argument ("-time", action="store_true",
                help="show timeouts only")
        aparser.add_argument ("-mem", action="store_true",
                help="show memory outs only")
        aparser.add_argument ("-err", action="store_true",
                help="show errors only")
        aparser.add_argument ("-ok", action="store_true",
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
        aparser.add_argument ("--no-colors", action="store_true",
                              help="disable colors")
        g_args = aparser.parse_args()

        # do not use a set here as the order of directories should be preserved
        unique_dirs = []
        for d in g_args.dirs:
            if d not in unique_dirs:
                unique_dirs.append(d)
        g_args.dirs = unique_dirs

        if len(g_args.dirs) < 1:
            raise CmpSMTException ("invalid number of dirs given")

        for d in g_args.dirs:
            if not os.path.isdir(d):
                raise CmpSMTException ("given smt run is not a directory")

        if g_args.bs:
            g_args.columns = \
                    "status,lods,calls,time_sat,time_rw,time_beta"
        elif g_args.dp:
            g_args.columns = \
                    "status,lods,time_time,time_app,time_sapp"
        elif g_args.M:
            g_args.columns = \
                    "status,lods,models_bvar,models_arr,"\
                    "time_time,time_sat"
            g_args.m = True
        
        if not g_args.m:
            for x in list(FILTER_OUT.keys()):
                del g_file_stats[x]

        g_args.columns = g_args.columns.split(',')
        for c in g_args.columns:
            if c not in FILE_STATS_KEYS:
                raise CmpSMTException("column '{}' not available".format(c))

        if g_args.show_all:
            g_args.columns = FILE_STATS_KEYS

        if g_args.no_colors:
            COLOR_BEST = ''
            COLOR_DIFF = ''
            COLOR_DISC = ''
            COLOR_STAT = ''
            COLOR_NOCOLOR = ''

        _read_data (g_args.dirs)
        _pick_data ()
        _compute_totals()
        _print_data ()

    except KeyboardInterrupt as e:
        sys.exit ("[cmpsmt] interrupted")
    except CmpSMTException as e:
        sys.exit (str(e))

