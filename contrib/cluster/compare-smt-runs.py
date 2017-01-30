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
g_benchmarks = set() 
g_parse_err_only = False

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

def _get_name_and_ext (fname):
    return ("".join(fname.rpartition('.')[:-2]), fname.rpartition('.')[-1])

def _is_float(s):
    return s.lstrip('-').replace('.', '', 1).isdigit()

def _is_int(s):
    if isinstance(s, int):
        return True
    return s.lstrip('-').isdigit()

def _is_number(s):
    return _is_float(s)

# compatibility for older boolector versions with different statistics format
def select_column(line, old_pos):
    cols = line.split()
    # check if there is a number at 'old_pos'
    if _is_number(cols[old_pos]):
        return cols[old_pos]
    return cols[1]

# per directory/file flag
# column_name : <colname>, <keyword>, <filter>
FILTER_LOG = [
  # bit blasting stats
  ('cnf_vars',
   'CNF VARs',
   lambda x: 'CNF variables' in x and 'core' in x,
   lambda x: select_column(x, 3)),
  ('cnf_clauses',
   'CNF CLAUSEs',
   lambda x: 'CNF clauses' in x and 'core' in x,
   lambda x: select_column(x, 3)),
  ('aig_vars',
   'AIG VARs',
   lambda x: 'AIG variables' in x and 'core' in x,
   lambda x: select_column(x, 3)),
  ('aig_ands',
   'AIG ANDs',
   lambda x: 'AIG ANDs' in x and 'core' in x,
   lambda x: select_column(x, 4)),
  # lemmas on demand stats
  ('lods',
   'LODS', 
   lambda x: 'LOD refinements' in x,
   lambda x: select_column(x, 3)),
  ('refiter',
   'REFS', 
   lambda x: 'refinement iterations' in x,
   lambda x: select_column(x, 1)),
  ('lods_avg',
   'LODS avg',
   lambda x: 'average lemma size' in x,
   lambda x: select_column(x, 4)),
  ('lods_fc',
   'LODS FC',
   lambda x: 'function congruence conf' in x,
   lambda x: select_column(x, 4)),
  ('lods_br',
   'LODS BR',
   lambda x: 'beta reduction conf' in x,
   lambda x: select_column(x, 4)),
  ('calls',
   'CALLS', 
   lambda x: 'SAT calls' in x, 
   lambda x: select_column(x, 1)),
  ('num_beta',
   'BETA', 
   lambda x: 'beta reductions' in x and 'partial' not in x,
   lambda x: select_column(x, 3)),
  ('num_eval',
   'EVAL', 
   lambda x: 'evaluations' in x,
   lambda x: select_column(x, 3)),
  ('num_prop',
   'PROP', 
   lambda x: 'slvfun' in x and 'propagations' in x and 'down' not in x,
   lambda x: select_column(x, 2)),
  ('num_propd',
   'PROPD', 
   lambda x: 'propagations down' in x,
   lambda x: select_column(x, 3)),
  ('num_fvars', 
   'FVAR',
   lambda x: 'dual prop: failed vars' in x,
   lambda x: select_column(x, 5)),
  ('num_fapps',
   'FAPP',
   lambda x: 'dual prop: failed applies' in x,
   lambda x: select_column(x, 5)),
  # sls stats
  ('num_moves', 
   'MOVES',
   lambda x: 'moves' in x,
   lambda x: select_column(x, 2)),
  ('num_props',
   'PROPS',
   lambda x: 'propagation (steps)' in x,
   lambda x: select_column(x, 3)),
  ('num_conf_rec', 
   'CONF(REC)',
   lambda x: 'propagation move conflicts (recoverable)' in x,
   lambda x: select_column(x, 5)),
  ('num_conf_non_rec',
   'CONF(NON-REC)',
   lambda x: 'propagation move conflicts (non-recoverable)' in x,
   lambda x: select_column(x, 5)),
  ('num_cegqi_refs',
   'CEGQI R',
   lambda x: 'cegqi solver refinements' in x,
   lambda x: select_column(x, 4)),
  # time stats
  ('time_clapp',
   'CLONE[s]', 
   lambda x: 'cloning for initial applies search' in x,
   lambda x: select_column(x, 1)),
  ('time_sapp',
   'SATDP[s]', 
   lambda x: 'seconds SAT solving' in x,
   lambda x: select_column(x, 1)),
  ('time_app',
   'APP[s]', 
   lambda x: 'seconds initial applies search' in x,
   lambda x: select_column(x, 1)),
  ('time_coll', 
   'COL[s]', 
   lambda x: 'collecting initial applies' in x, 
   lambda x: select_column(x, 1)),
  ('time_sat',
   'SAT[s]', 
   lambda x: 'pure SAT' in x, 
   lambda x: select_column(x, 1)),
  ('time_rw',
   'RW[s]', 
   lambda x: 'rewriting engine' in x, 
   lambda x: select_column(x, 1)),
  ('time_beta',
   'BETA[s]', 
   lambda x: 'beta-reduction' in x, 
   lambda x: select_column(x, 1)),
  ('time_eval',
   'EVAL[s]', 
   lambda x: 'seconds expression evaluation' in x,
   lambda x: select_column(x, 1)),
  ('time_pas',
   'PAS[s]', 
   lambda x: 'propagation apply search' in x,
   lambda x: select_column(x, 1)),
  ('time_qi',
   'QI[s]', 
   lambda x: 'seconds quantifier instantiation' in x,
   lambda x: select_column(x, 1)),
  ('time_dqi',
   'DQI[s]', 
   lambda x: 'seconds dual quantifier instantiation' in x,
   lambda x: select_column(x, 1)),
  ('time_sy',
   'SY[s]', 
   lambda x: 'seconds synthesizing' in x,
   lambda x: select_column(x, 1)),
  ('time_dsy',
   'DSY[s]', 
   lambda x: 'seconds dual synthesizing' in x,
   lambda x: select_column(x, 1)),
]

def _read_status(line):
    status = line.split(':')[1].strip()
    if 'ok' in status:
        return 'ok'
    elif 'time' in status:
        return 'time'
    elif 'memory' in status:
        return 'mem'
    elif 'segmentation' in status:
        return 'segf'
    elif 'signal' in status:
        return 'sig'
    else:
        raise CmpSMTException("invalid status: '{}'".format(status))


# column_name : <colname>, <keyword>, <filter>, <format>
FILTER_ERR = [
  ('status',
   'STAT', 
   lambda x: 'runlim' in x and 'status:' in x,
   _read_status),
  ('result',
   'RES', 
   lambda x: 'runlim' in x and 'result:' in x,
   lambda x: x.split()[2]),
  ('time_real',
   'REAL[s]', 
   lambda x: 'runlim' in x and 'real:' in x,
   lambda x: x.split()[2]),
  ('time_cpu',
   'CPU[s]', 
   lambda x: 'runlim' in x and 'time:' in x,
   lambda x: x.split()[2]),
  ('space',
   'SPACE[MB]', 
   lambda x: 'runlim' in x and 'space:' in x,
   lambda x: x.split()[2]),
]

# these columns will be computed in _normalize_data
GROUP_COLUMNS = {
  'g_solved': 'SLVD', 
  'g_total':  'TOT', 
  'g_time':   'TO', 
  'g_mem':    'MO', 
  'g_err':    'ERR', 
  'g_sat':    'SAT', 
  'g_unsat':  'UNSAT', 
  'g_uniq':   'UNIQ',
}

# column_name : <colname>, <keyword>, <filter>, [<is_dir_stat>] (optional)
FILTER_OUT = [
  ('models_arr',  'MARR', lambda x: '[' in x, lambda x: 1),
  ('models_bvar', 'MVAR', lambda x: '[' not in x, lambda x: 1)
]

filter_log_keys = set([t[0] for t in FILTER_LOG])
filter_err_keys = set([t[0] for t in FILTER_ERR])
filter_out_keys = set([t[0] for t in FILTER_OUT])

filter_log_dict = dict([(t[0], t[1:]) for t in FILTER_LOG])
filter_err_dict = dict([(t[0], t[1:]) for t in FILTER_ERR])
filter_out_dict = dict([(t[0], t[1:]) for t in FILTER_OUT])

assert(filter_log_keys.isdisjoint(filter_err_keys))
assert(filter_log_keys.isdisjoint(filter_out_keys))
assert(filter_err_keys.isdisjoint(filter_out_keys))

STATS_KEYS = [t[0] for t in FILTER_LOG]
STATS_KEYS.extend([t[0] for t in FILTER_ERR])
STATS_KEYS.extend([t[0] for t in FILTER_OUT])
STATS_KEYS.extend(GROUP_COLUMNS.keys())

g_file_stats = {}
g_total_stats = {}

def _format_status(l):
    if 'err' in l:
        return 'err'
    elif 'ok' in l:
        return 'ok'
    return ''.join(set(l))

g_format_column_sum = {
    'status' : _format_status,
}

def _cast(s):
    if _is_int(s):
        return int(s)
    elif _is_float(s):
        return float(s)
    return s

def _filter_data(d, file, filters):
    global g_file_stats
    
    (f_name, f_ext) = _get_name_and_ext(file)

    for t in filters:
        k = t[0]
        if k not in g_file_stats:
            g_file_stats[k] = {}
        if d not in g_file_stats[k]:
            g_file_stats[k][d] = {}
        if f_name not in g_file_stats[k][d]:
            g_file_stats[k][d][f_name] = None

    if os.stat(os.path.join(d, file)).st_size == 0:
        return

    used_filters = set()
    with open(os.path.join(d, file), 'r') as infile:
        lines = infile.readlines()
        for line in reversed(lines):
            line = line.strip()

            if len(used_filters) == len(filters):
                break

            for t in filters:
                assert(len(t) == 4)

                k = t[0]
                # value already extracted for current file
                if k in used_filters:
                    continue

                f_match = t[2]
                f_val = t[3]
                
                if not f_match(line):
                    continue

                val = _cast(f_val(line))
                used_filters.add(k)

                if f_ext == 'out' \
                   and line in ('sat', 'unsat', 'unknown'): 
                       continue

                assert(g_file_stats[k][d][f_name] == None)
                g_file_stats[k][d][f_name] = val 



def _read_log_file(d, f):
    _filter_data(d, f, FILTER_LOG)


def _read_err_file(d, f):
    global g_file_stats

    try:
        _filter_data(d, f, FILTER_ERR)
    except CmpSMTException as e:
        raise CmpSMTException("{} in file {}".format(str(e), f))

def _init_missing_files(data):
    global g_benchmarks

    for k in data:
        for d in g_args.dirs:
            for f in g_benchmarks:
                if d not in data[k]:
                    data[k][d] = {}
                if f not in data[k][d]:
                    data[k][d][f] = None

def _normalize_data(data):
    global g_args

    assert('result' in data)

    # reset timeout if given
    if g_args.timeout:
        for d in data['time_cpu']:
            for f in data['time_cpu'][d]:
                if data['time_cpu'][d][f] is None or \
                   data['time_cpu'][d][f] > g_args.timeout[d]:
                    data['time_cpu'][d][f] = g_args.timeout[d]
                    data['status'][d][f] = "time"
                    data['result'][d][f] = 1


    # initialize group columns derived from status
    for k in ['g_solved', 'g_total', 'g_time', 'g_mem', 'g_err',
              'g_sat','g_unsat']:
        assert(k not in data)
        data[k] = {}
        for d in data['status']:
            assert(d not in data[k])
            data[k][d] = {}
            for f in data['status'][d]:
                assert(f not in data[k][d])
                if k == 'g_total':
                    data[k][d][f] = 1
                else:
                    data[k][d][f] = 0

    # compute values for group columns derived from status
    for d in data['status']:
        for f in data['status'][d]:
            s = data['status'][d][f] 
            r = data['result'][d][f]

            if s == 'ok' and r in (10, 20):
                data['g_solved'][d][f] = 1
                if r == 10:
                    data['g_sat'][d][f] = 1
                else:
                    assert(r == 20)
                    data['g_unsat'][d][f] = 1
            elif s == 'time':
                data['g_time'][d][f] = 1
            elif s == 'mem':
                data['g_mem'][d][f] = 1
                if g_args.pen:
                    data['time_cpu'][d][f] = g_args.pen
            else:
                data['status'][d][f] = 'err'
                data['g_err'][d][f] = 1
                if g_args.pen:
                    data['time_cpu'][d][f] = g_args.pen
                        

    # collect data for virtual best solver
    if g_args.vb:
        if g_args.vbp:
            bdir = g_args.dirs[0]   # base run
            prep_dirs = g_args.dirs[1:] # "preprocessing" runs

            for pdir in prep_dirs:
                vbpdir = "{} + {}".format(_base_dir(bdir), _base_dir(pdir))

                # initialize for virtual best solver
                for k in data.keys():
                    if vbpdir not in data[k]:
                        data[k][vbpdir] = {}

                for f in g_benchmarks:
                    if data["time_cpu"][bdir][f] < g_args.timeout[bdir]:
                        time_bdir = data["time_cpu"][bdir][f]
                    else:
                        time_bdir = g_args.timeout[bdir]

                    if data["time_cpu"][pdir][f] < g_args.timeout[pdir]:
                        time_pdir = data["time_cpu"][pdir][f]
                    else:
                        time_pdir = g_args.timeout[pdir]

                    if data["status"][pdir][f] in ["ok", "time"] \
                       and time_pdir < g_args.timeout[pdir]:
                        for k in data.keys():
                            data[k][vbpdir][f] = data[k][pdir][f]
                    elif data["status"][bdir][f] == "ok":
                        for k in data.keys():
                            data[k][vbpdir][f] = data[k][bdir][f]
                        time_vbp = round(time_bdir + g_args.timeout[pdir], 2)
                        data["time_cpu"][vbpdir][f] = time_vbp
                        if time_vbp >= g_args.timeout[bdir]:
                            data["status"][vbpdir][f] = "time"
                            data["time_cpu"][vbpdir][f] = g_args.timeout[bdir]
                            if not g_args.g:
                                data["result"][vbpdir][f] = 1
                    else:
                        for k in data.keys():
                            data[k][vbpdir][f] = data[k][bdir][f]
                g_args.dirs.append(vbpdir)
        else:
            vb_dir = "virtual best solver (portfolio)"

            for f in g_benchmarks:
                v = []
                for d in g_args.dirs:
                    if data['time_cpu'][d][f] is not None \
                        and data['status'][d][f] == 'ok':
                        v.append((data['time_cpu'][d][f], d))
                v = sorted(v)

                best_dir = None
                if len(v) > 0:
                    best_dir = v[0][1]
                for k in data.keys():
                    if vb_dir not in data[k]:
                        data[k][vb_dir] = {}
                    if best_dir is None:
                        data[k][vb_dir][f] = None
                    else:
                        data[k][vb_dir][f] = data[k][best_dir][f]
            g_args.dirs.append(vb_dir)


    # add uniquely solved column
    if g_args.u:
        data['g_uniq'] = {}
        for f in g_benchmarks:
            stats = []
            for d in data['status']:
                if d not in data['g_uniq']:
                    data['g_uniq'][d] = {}
                data['g_uniq'][d][f] = 0
                if data['status'][d][f] == 'ok':
                    stats.append(d)

            if len(stats) == 1:
                data['g_uniq'][stats[0]][f] = 1

def _read_out_file(d, f):
    _filter_data(d, f, FILTER_OUT)

def _save_cache_file(dir):
    global g_file_stats

    sum_filename = "{}/cache".format(dir)
    keys = sorted(g_file_stats.keys())
    files = [] 
    for f in g_file_stats[keys[0]][dir]:
        files.append(f)

    with open(sum_filename, "w") as sum_file: 
        sum_file.write("{}\n".format(" ".join(keys)))
        for f in sorted(files):
            data = []
            for k in keys:
                data.append(str(g_file_stats[k][dir][f]))
            sum_file.write("{} {}\n".format(f, " ".join(data)))

def _read_cache_file(dir):
    global g_file_stats, g_benchmarks

    sum_filename = "{}/cache".format(dir)
    if os.path.isfile(sum_filename):
        with open(sum_filename, "r") as sum_file:
            keys = None
            for line in sum_file:
                # initialize keys
                if keys is None:
                    keys = line.split()

                    expected_keys = list(filter_err_keys)
                    if not g_parse_err_only:
                        expected_keys.extend(filter_log_keys)
                        if g_args.m:
                            expected_keys.extend(filter_out_keys)

                    missing_keys = set(expected_keys) - set(keys)
                    if len(missing_keys) > 0:
                        print("column(s) {} missing for directory '{}'. "\
                              "extracting data from files".format(
                                  list(missing_keys), dir))
                        return False
                else:
                    cols = line.split()
                    f = cols[0]
                    if f not in g_benchmarks:
                        g_benchmarks.add(f)
                    data = cols[1:]
                    assert(len(data) == len(keys))
                    for i in range(len(keys)):
                        k = keys[i]
                        assert(k in STATS_KEYS)
                        if k not in g_file_stats:
                            g_file_stats[k] = {}
                        if dir not in g_file_stats[k]:
                            g_file_stats[k][dir] = {}
                        if k in filter_log_dict:
                            t = filter_log_dict[k]
                        else:
                            assert(k in filter_err_dict)
                            t = filter_err_dict[k]
                        assert(len(t) == 3)
                        assert(f not in g_file_stats[k][dir])
                        if data[i] == "None":
                            g_file_stats[k][dir][f] = None
                        else:
                            g_file_stats[k][dir][f] = _cast(data[i])
            return True
    return False 

def _read_data (dirs):
    for d in dirs:
        # read cached data
        if _read_cache_file(d):
            continue
        # extract data from files
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
                    if f_name not in g_benchmarks:
                        g_benchmarks.add(f_name)
                    _read_err_file (d, "{}{}".format(f[:-3], "err"))
                    # do not extract data from log file if only data from error
                    # file is required
                    if not g_parse_err_only:
                        _read_log_file (d, f)
                        if g_args.m:
                            outfile = "{}{}".format(f[:-3], "out")
                            if not os.path.isfile(os.path.join (d, outfile)):
                                raise CmpSMTException ("missing '{}'".format (
                                    os.path.join (d, outfile)))
                            _read_out_file (d, "{}{}".format(f[:-3], "out"))
        # create cache file
        _save_cache_file(d)

def _pick_data(benchmarks, data):
    global g_args

    sort_reverse = False
    f_cmp = lambda x, y: x * (1 + g_args.diff) <= y
    if g_args.cmp_col == 'g_solved':
        sort_reverse = True 
        f_cmp = lambda x, y: x > y

    best_stats = {}
    diff_stats = {}

    k = g_args.cmp_col
    for f in benchmarks:
        v = sorted(\
            [(data[k][d][f], d) \
                for d in g_args.dirs if data[k][d][f] is not None],
            reverse=sort_reverse)

        # strings are not considered for diff/best values
        if len(v) == 0 or isinstance(v[0][0], str):
            best_stats[f] = None
            diff_stats[f] = None
            continue

        best_dir = v[0][1]

        if len(set([t[0] for t in v])) <= 1:
            best_stats[f] = None
            if g_args.cmp_col == 'g_solved':
                x = sorted(\
                    [(data['time_cpu'][d][f], d) \
                        for d in g_args.dirs \
                            if data['time_cpu'][d][f] is not None])
                if len(set([t[0] for t in x])) > 1:
                    best_stats[f] = x[0][1]
        else:
            best_stats[f] = best_dir

        if best_stats[f] is None or not f_cmp(v[0][0], v[1][0]):
            diff_stats[f] = None
        else:
            diff_stats[f] = best_dir

    assert(diff_stats.keys() == best_stats.keys())
    return diff_stats, best_stats


def _format_field(field, width, color=None, colspan=0, classes=[]):
    field = "-" if field is None \
                            or (g_args.vbsd \
                                and not isinstance(field, str) \
                                and color != COLOR_DIFF \
                                and color != COLOR_BEST) \
                else str(field)
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

    if g_args.plain:
        print("{}".format(" ".join(formatted_cols)))
    elif g_args.html:
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


def _print_html_footer():
    print("<tbody></table></body></html>")


def _has_status(status, f):
    return status in set(g_file_stats['status'][d][f] for d in g_args.dirs)

def _get_column_name(key):
    if key in filter_log_dict:
        return filter_log_dict[key][0]
    elif key in filter_err_dict:
        return filter_err_dict[key][0]
    elif key in GROUP_COLUMNS:
        return GROUP_COLUMNS[key]
    assert(key in filter_out_dict)
    return filter_out_dict[key][0]


def _get_color(f, d, diff_stats, best_stats):
    global g_args
    if diff_stats[f] == d:
        return COLOR_DIFF
    elif best_stats[f] == d:
        return COLOR_BEST
    return COLOR_NOCOLOR


def _get_group_totals():
    global g_args, g_benchmarks, g_file_stats, g_format_column_sum
    stats = {}
    totals = {}

    # collect statistics per group
    for f in g_benchmarks:
        group_name = f.split('-')[0]

        if group_name not in stats:
            stats[group_name] = {} 

        if 'totals' not in stats:
            stats['totals'] = {}

        group = stats[group_name]
        for d in g_args.dirs:
            if d not in group:
                group[d] = {}
            if d not in stats['totals']:
                stats['totals'][d] = {}

            for stat in g_file_stats:
                if stat not in group[d]:
                    group[d][stat] = []
                if stat not in stats['totals'][d]:
                    stats['totals'][d][stat] = []
                val = g_file_stats[stat][d][f]
                # val is None if file does not exist or all files in 
                # a group timed out for virtual best solver
                if val is not None:
                    group[d][stat].append(val)
                    stats['totals'][d][stat].append(val)

    # compute group totals
    for k in g_file_stats:
        assert(k not in totals)
        totals[k] = {}
        for d in g_args.dirs:
            if d not in totals[k]:
                totals[k][d] = {}

            for group in stats:
                assert(group not in totals[k][d])
                if k in g_format_column_sum:
                    val = g_format_column_sum[k](stats[group][d][k])
                else:
                    try:
                        val = sum(stats[group][d][k])
                    except TypeError:
                        val = None
                    if isinstance(val, float):
                        val = round(val, 1)
                totals[k][d][group] = val 

    return totals, stats.keys()


def _base_dir(path):
    return os.path.basename(path.rstrip('/'))


def _print_totals():

    data, benchmarks = _get_group_totals()

    if 'result' in data:
        del(data['result'])

    benchmark_column_width, header_column_widths, data_column_widths = \
        _get_column_widths(data, benchmarks)

    # g_args.columns and data.keys() may differ, just use the ones in data
    # do not use data.keys() here since we want to keep the order of
    # g_args.columns
    columns = [k for k in g_args.columns if k in data.keys()]

    if not g_args.html:
        print("\n")

    # header
    cols = ["DIRECTORY"]
    cols.extend(_get_column_name(k) for k in columns)
    widths = [max(len(_base_dir(d)) for d in g_args.dirs)]
    widths.extend([max(data_column_widths[k][d] for d in g_args.dirs) \
                      for k in columns])
    classes = [["header"] for i in range(len(columns) + 1)]
    _print_row(cols, widths, classes=classes)

    # totals
    for d in g_args.dirs:
        cols = [_base_dir(d)]
#            classes.append([["borderleft"]])
#            classes[-1].extend([[] for i in range(len(g_args.columns) - 1)])
        cols.extend(data[k][d]['totals'] for k in columns)
        _print_row(cols, widths)#, classes=classes)
    if g_args.html:
        print("</table><br><br><table>")
    else:
        print("\n\n")

def _get_column_widths(data, benchmarks):
    global g_args

    # g_args.columns and data.keys() may differ, just use the ones in data
    # do not use data.keys() here since we want to keep the order of
    # g_args.columns
    columns = [k for k in g_args.columns if k in data.keys()]

    padding = 1
    benchmark_column_width = \
        padding + max(max(len(b) for b in benchmarks), len("DIRECTORY"))

    data_column_widths = dict((k, {}) for k in g_args.columns)
    for d in g_args.dirs:
        for k in columns:
            data_column_widths[k][d] = \
                padding + \
                max(len(_get_column_name(k)),
                    max(len(str(v)) for v in data[k][d].values()))


    # header column widths
    column_groups = dict((d, list(columns)) for d in g_args.dirs)
    header_column_widths = {} 
    for d, g in column_groups.items():
        width_cols = 0
        for k in g:
            width_cols += data_column_widths[k][d]
        width_dir = len(_base_dir(d))
        if width_cols > width_dir or g_args.plain:
            header_column_widths[d] = width_cols
        else:
            header_column_widths[d] = width_dir
            # add width to first column of column group if directory name is
            # longer than the column group itself
            data_column_widths[columns[0]][d] += width_dir - width_cols 

    return benchmark_column_width, header_column_widths, data_column_widths


def _print_data ():
    global g_file_stats

    diff_stats, best_stats = _pick_data(g_benchmarks, g_file_stats)
    if g_args.g:
        data, benchmarks = _get_group_totals()
        diff_stats, best_stats = _pick_data(benchmarks, data)
    else:
        data = g_file_stats
        benchmarks = g_benchmarks

    benchmark_column_width, header_column_widths, data_column_widths = \
        _get_column_widths(data, benchmarks)

    if g_args.html:
        _print_html_header()
        print("""<table id="legend">
                   <tr>
                     <th>LEGEND</th>
                     <td class="best">best value</td>
                     <td class="diff">difference of '{}' >= {}</td>
                     <td class="disc">discrepancy</td>
                     <td class="stat">status differs</td>
                   </tr>
                 </table><table>""".format(g_args.cmp_col, g_args.diff))

    if g_args.t or g_args.html:
        _print_totals()
        
    # print header
    columns = ["DIRECTORY"]
    columns.extend([_base_dir(d) for d in g_args.dirs])
    widths = [benchmark_column_width]
    widths.extend([header_column_widths[d] for d in g_args.dirs])
    colspans = [0]
    colspans.extend([len(g_args.columns) for d in g_args.dirs])

    classes = [["header"]]
    classes.extend([["borderleft", "header"] for d in g_args.dirs])
    if not g_args.plain:
        _print_row (columns, widths, colspans=colspans, classes=classes)

    columns = ["BENCHMARK"]
    widths = [benchmark_column_width]
    classes = [["header"]]

    for d in g_args.dirs:
        classes.append([["header"] for k in g_args.columns])
        classes[-1][0].append("borderleft")
        columns.append([_get_column_name(k) for k in g_args.columns])
        widths.append([data_column_widths[k][d] for k in g_args.columns])
    if not g_args.plain:
        _print_row (columns, widths, classes=classes)

    if g_args.html:
        print("</thead><tbody>")

    # print data rows
    rows = sorted(benchmarks, key=lambda s: s.lower())
    # totals row should always be on the bottom
    if g_args.g:
        assert ('totals' in rows)
        rows.remove('totals')
        rows.append('totals')
    for f in rows:
        if not g_args.g:
            if g_args.timeof \
               and not g_file_stats['status'][g_args.timeof][f] == 'time':
                continue
            if g_args.time and not _has_status('time', f):
                continue
            if g_args.err and not _has_status('err', f):
                continue
            if g_args.ok and not _has_status('ok', f):
                continue
            if g_args.mem and not _has_status('mem', f):
                continue

        s = None
        r = None
        if 'status' in data:
            s = [data['status'][d][f] for d in g_args.dirs \
                                      if data['status'][d][f]]
        if 'result' in data:
            r = [data['result'][d][f] for d in g_args.dirs \
                                      if data['result'][d][f]]

        # show discrepancies only
        if g_args.dis and r is not None:
            r_tmp = [x for x in r if x == 10 or x == 20]
            # no discrepancy, skip
            if len(set(r_tmp)) == 1: continue

        # highlight row if status is not the same or solvers are disagreeing
        color = COLOR_STAT \
                if not g_args.vbsd and s is not None and len(set(s)) > 1 \
                else (COLOR_DISC if (not g_args.g
                                     and (not g_args.vbsd \
                                      or (g_args.vbsd \
                                          and (s is None or len(set(s)) <= 1)))\
                                     and r is not None \
                                     and len(set(r)) > 1) \
                                 else COLOR_NOCOLOR)
        columns = [f]
        widths = [benchmark_column_width]
        colors = [color]
        classes = [["nowrap"]]

        for d in g_args.dirs:
            classes.append([["borderleft"]])
            classes[-1].extend([[] for i in range(len(g_args.columns) - 1)])
            columns.append([data[k][d][f] for k in g_args.columns])
            widths.append([data_column_widths[k][d] for k in g_args.columns])
            colors.append(color if color != COLOR_NOCOLOR \
                        else _get_color(f, d, diff_stats, best_stats))

        _print_row(columns, widths, colors=colors, classes=classes)

    if g_args.html:
        _print_html_footer()


def _filter_common(data):
    global g_benchmarks

    remove = []

    for f in g_benchmarks:
        s = set([data['status'][d][f] for d in g_args.dirs])
        if 'ok' not in s or len(s) != 1:
            remove.append(f)

    for f in remove:
        g_benchmarks.remove(f)


if __name__ == "__main__":
    try:
        aparser = ArgumentParser(
                      formatter_class=ArgumentDefaultsHelpFormatter,
                      epilog="availabe values for column: {{ {} }}, " \
                             "note: {{ {} }} are enabled for '-M' only.".format(
                          ", ".join(sorted(STATS_KEYS)),
                          ", ".join(sorted(filter_out_keys))))
        aparser.add_argument \
              (
                "-f",
                metavar="string", dest="filter", type=str, default=None,
                help="filter benchmark files by <string>"
              )
        aparser.add_argument \
              (
                "-to",
                metavar="seconds[,second ...]", dest="timeout", default=None,
                help="use individual time out"
              )
        aparser.add_argument \
              (
                "-vb",
                action="store_true",
                help="generate virtual best solver"
              )
        aparser.add_argument \
              (
                "-vbp",
                action="store_true",
                help="generate virtual best solver out of two runs with " \
                     "one treated as a preprocessing step (don't forget to " \
                     "provide a list " \
                     "of timeouts via -to in the same order as the runs, " \
                     "the run with the lesser timeout serves as " \
                     "preprocessing step)"
              )
        aparser.add_argument \
              (
                "--vb-show-details",
                dest="vbsd", action="store_true",
                help="show detailed overview for virtual best solver"
               )
        aparser.add_argument \
              (
                "-hd",
                metavar="float", dest="diff", type=float, default=0.1,
                help="highlight diff if greater than <float>"
              )
        aparser.add_argument \
              (
                "-bs",
                action="store_true",
                help="compare boolector statistics"
              )
        aparser.add_argument \
              (
                "-dp",
                action="store_true",
                help = "compare dual prop statistics"
              )
        aparser.add_argument \
              (
                "-m",
                action="store_true",
                help="extract models statistics"
              )
        aparser.add_argument \
              (
                "-M",
                action="store_true",
                help="compare models statistics"
              )
        aparser.add_argument \
              (
                "-dis",
                action="store_true",
                help="show discrepancies only"
              )
        aparser.add_argument \
              (
                "-time",
                action="store_true",
                help="show timeouts only"
              )
        aparser.add_argument \
              (
                "-toof",
                metavar="dir", dest="timeof", action="store", default=None,
                help="show timeouts of given dir only"
              )
        aparser.add_argument \
              (
                "-mem",
                action="store_true",
                help="show memory outs only"
              )
        aparser.add_argument \
              (
                "-err",
                action="store_true",
                help="show errors only"
              )
        aparser.add_argument \
              (
                "-ok",
                action="store_true",
                help="show non-errors only"
              )
        aparser.add_argument \
              (
                "-c",
                metavar="column", dest="cmp_col",
                choices=STATS_KEYS,
                help="compare results column"
              )
        aparser.add_argument \
              (
                "-s",
                metavar="column[,column ...]", dest="columns",
                help="list of columns to print"
              )
        aparser.add_argument \
              (
                "-a",
                dest="show_all", action="store_true",
                help="print all columns"
              )
        aparser.add_argument \
              (
                "--html",
                action="store_true",
                help="generte html output"
              )
        aparser.add_argument \
              (
                "dirs",
                nargs=REMAINDER,
                help="two or more smt run directories to compare"
              )
        aparser.add_argument \
              (
                "--no-colors",
                action="store_true",
                help="disable colors"
              )
        aparser.add_argument \
              (
                "-g",
                action="store_true",
                help="group benchmarks into families"
              )
        aparser.add_argument \
              (
                "-u",
                action="store_true",
                help="uniquely solved instances"
              )
        aparser.add_argument \
              (
                "-t",
                action="store_true",
                help="show totals table"
              )
        aparser.add_argument \
              (
                "-p",
                dest="plain", action="store_true",
                help="plain mode, only show columns and " \
                     "filename (for gnuplot data files)"
              )
        aparser.add_argument \
              (
                "-common",
                dest="common", action="store_true",
                help="show commonly solved instances only"
              )
        aparser.add_argument \
              (
                "-pen", type=int,
                metavar="seconds[,second ...]", dest="pen", default=None,
                help="CPU time penalty for memory out/error"
              )
        g_args = aparser.parse_args()

        # do not use a set here as the order of directories should be preserved
        unique_dirs = []
        for d in g_args.dirs:
            if d not in unique_dirs:
                unique_dirs.append(d)
        g_args.dirs = unique_dirs

        if len(g_args.dirs) < 1:
            raise CmpSMTException ("invalid number of dirs given")

        if g_args.cmp_col is None:
            if g_args.g:
                g_args.cmp_col = 'g_solved'
            else:
                g_args.cmp_col = 'time_cpu'

        if g_args.vbp: g_args.vb = True

        for d in g_args.dirs:
            if not os.path.isdir(d):
                raise CmpSMTException ("given smt run is not a directory")

        if g_args.columns is None:
            if g_args.g:
                g_args.columns = \
                    "status,result,g_solved,g_total,g_time,g_mem,g_err," \
                    "time_cpu,space"
            else:
                g_args.columns = "status,result,time_cpu,space"
            
        # column options
        if g_args.bs:
            g_args.columns = \
                    "status,lods,calls,time_sat,time_rw,time_beta"
        elif g_args.dp:
            g_args.columns = \
                    "status,lods,time_cpu,time_app,time_sapp"
        elif g_args.M:
            g_args.columns = \
                    "status,lods,models_bvar,models_arr,"\
                    "time_cpu,time_sat"
            g_args.m = True
            
        g_args.columns = g_args.columns.split(',')
        for c in g_args.columns:
            if c not in STATS_KEYS:
                raise CmpSMTException("column '{}' not available".format(c))

        if g_args.show_all:
            g_args.columns = STATS_KEYS

        if g_args.timeout:
            g_args.timeout = [float(s) for s in g_args.timeout.split(',')]
            if len(g_args.timeout) > 1 \
               and len(g_args.timeout) != len(g_args.dirs):
                   raise CmpSMTException ("invalid number of timeouts given")
            if g_args.timeout and len(g_args.timeout) == 1:
                g_args.timeout = [g_args.timeout[0] for d in g_args.dirs]
            assert (len(g_args.timeout) == len(g_args.dirs))    
            tmp = { g_args.dirs[i]:g_args.timeout[i] \
                    for i in range(0, len(g_args.dirs)) }
            g_args.timeout = tmp

        # some columns may not make sense or are not available for some options
        remove_columns = []
        if not g_args.m:
            remove_columns.extend(filter_out_keys)

        if g_args.g and 'result' in g_args.columns:
            remove_columns.append('result')

        for c in remove_columns:
            if g_args.columns.count(c) > 0:
                g_args.columns.remove(c)

        if g_args.u:
            g_args.columns.append('g_uniq')


        if len(g_args.columns) == 0:
            raise CmpSMTException ("no columns selected to display")
            

        if g_args.no_colors:
            COLOR_BEST = ''
            COLOR_DIFF = ''
            COLOR_DISC = ''
            COLOR_STAT = ''
            COLOR_NOCOLOR = ''

        if g_args.timeof and not g_args.timeof in g_args.dirs:
            raise CmpSMTException ("invalid dir given")

        if len(set(g_args.columns).intersection(filter_log_keys)) == 0:
            g_parse_err_only = True

        _read_data(g_args.dirs)

        # remove files not to display
        if g_args.filter:
            for f in g_benchmarks.copy():
                if g_args.filter not in str(f):
                    g_benchmarks.remove(f)

        if len(g_file_stats.keys()) > 0:
            _init_missing_files (g_file_stats)
            _normalize_data(g_file_stats)

            if g_args.common:
                _filter_common (g_file_stats)

            _print_data ()
        else:
            if g_args.filter:
                print("no files found that match '{}'".format(g_args.filter))
            else:
                print("no files found")

    except KeyboardInterrupt as e:
        sys.exit ("[cmpsmt] interrupted")
    except CmpSMTException as e:
        sys.exit (str(e))

