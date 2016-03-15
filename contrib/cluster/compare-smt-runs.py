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


# per directory/file flag
# column_name : <colname>, <keyword>, <filter>, <is_dir_stat>
FILTER_LOG = {
  'lods':       ['LODS', 
                 lambda x: b'LOD' in x, 
                 lambda x: x.split()[3], 
                 lambda x: int(x),
                 False],
  'lods_avg':   ['LODS avg',
                 lambda x: b'average lemma size' in x,
                 lambda x: x.split()[4],
                 lambda x: float(x),
                 False],
  'lods_fc':   ['LODS FC',
                 lambda x: b'function congruence conf' in x,
                 lambda x: x.split()[4],
                 lambda x: int(x),
                 False],
  'lods_br':   ['LODS BR',
                 lambda x: b'beta reduction conf' in x,
                 lambda x: x.split()[4],
                 lambda x: int(x),
                 False],
  'calls':      ['CALLS', 
                 lambda x: b'SAT calls' in x, 
                 lambda x: x.split()[1], 
                 lambda x: int(x),
                 False],
  'time_sat':   ['SAT[s]', 
                 lambda x: b'pure SAT' in x, 
                 lambda x: x.split()[1], 
                 lambda x: float(x),
                 False],
  'time_rw':    ['RW[s]', 
                 lambda x: b'rewriting engine' in x, 
                 lambda x: x.split()[1],
                 lambda x: float(x),
                 False],
  'time_beta':  ['BETA[s]', 
                 lambda x: b'beta-reduction' in x, 
                 lambda x: x.split()[1],
                 lambda x: float(x),
                 False],
  'time_eval':  ['EVAL[s]', 
                 lambda x: b'seconds expression evaluation' in x,
                 lambda x: x.split()[1], 
                 lambda x: float(x),
                 False],
  'time_lle':   ['LLE[s]', 
                 lambda x: b'lazy lambda encoding' in x,
                 lambda x: float(x.split()[1]), 
                 lambda x: float(x),
                 False],
  'time_pas':   ['PAS[s]', 
                 lambda x: b'propagation apply search' in x,
                 lambda x: x.split()[1], 
                 lambda x: float(x),
                 False],
  'time_pacs':   ['PAS[s]',
                 lambda x: b'propagation apply in conds search' in x,
                 lambda x: x.split()[1],
                 lambda x: float(x),
                 False],
  'time_neas':  ['NEAS[s]', 
                 lambda x: b'not encoded apply search' in x,
                 lambda x: x.split()[1], 
                 lambda x: float(x),
                 False],
  'num_beta':   ['BETA', 
                 lambda x: b'beta reductions:' in x,
                 lambda x: x.split()[3], 
                 lambda x: int(x),
                 False],
  'num_eval':   ['EVAL', 
                 lambda x: b'evaluations:' in x,
                 lambda x: x.split()[3], 
                 lambda x: int(x),
                 False],
  'num_prop':   ['PROP', 
                 lambda x: b'propagations:' in x,
                 lambda x: x.split()[2], 
                 lambda x: int(x),
                 False],
  'num_propd':  ['PROPD', 
                 lambda x: b'propagations down:' in x,
                 lambda x: x.split()[3], 
                 lambda x: int(x),
                 False],
  'time_clapp': ['CLONE[s]', 
                 lambda x: b'cloning for initial applies search' in x,
                 lambda x: x.split()[1], 
                 lambda x: float(x),
                 False],
  'time_sapp':  ['SATDP[s]', 
                 lambda x: b'SAT solving for initial applies search' in x,
                 lambda x: x.split()[1], 
                 lambda x: float(x),
                 False],
  'time_app':   ['APP[s]', 
                 lambda x: b'seconds initial applies search' in x,
                 lambda x: x.split()[1], 
                 lambda x: float(x),
                 False],
  'time_coll':  ['COL[s]', 
                 lambda x: b'collecting initial applies' in x, 
                 lambda x: x.split()[1], 
                 lambda x: float(x),
                 False],
  'num_fvars':  ['FVAR',
          lambda x: b'dual prop: failed vars:' in x,
                 lambda x: x.split()[5],
                 lambda x: int(x),
                 False],
  'num_fapps':  ['FAPP',
                 lambda x: b'dual prop: failed applies:' in x,
                 lambda x: x.split()[5],
                 lambda x: int(x),
                 False]
}


def err_extract_status(line):
    status = line.split(b':')[1].strip()
    if b'ok' in status:
        return 'ok'
    elif b'time' in status:
        return 'time'
    elif b'memory' in status:
        return 'mem'
    elif b'segmentation' in status:
        return 'segf'
    elif b'signal' in status:
        return 'sig'
    else:
        raise CmpSMTException("invalid status: '{}'".format(status.decode()))


def err_extract_opts(line):
    opt = line.split()[2].decode()
    if opt[0] == '-':
        return opt
    return None 


# column_name : <colname>, <keyword>, <filter>, <format>, [<is_dir_stat>] (optional)
FILTER_ERR = {
  'status':    ['STAT', 
                lambda x: b'runlim' in x and b'status:' in x,
                err_extract_status,
                lambda x: str(x),
                False],
  'g_solved':  ['SLVD', 
                lambda x: b'runlim' in x and b'status:' in x,
                err_extract_status,
                lambda x: str(x),
                False],
  'g_total':   ['TOT', 
                lambda x: b'runlim' in x and b'status:' in x,
                err_extract_status,
                lambda x: str(x),
                False],
  'g_time':    ['TOUTS', 
                lambda x: b'runlim' in x and b'status:' in x,
                err_extract_status,
                lambda x: str(x),
                False],
  'g_mem':     ['MOUTS', 
                lambda x: b'runlim' in x and b'status:' in x,
                err_extract_status,
                lambda x: str(x),
                False],
  'g_err':     ['ERR', 
                lambda x: b'runlim' in x and b'status:' in x,
                err_extract_status,
                lambda x: str(x),
                False],
  'g_sat':     ['SAT', 
                lambda x: b'runlim' in x and b'result:' in x,
                lambda x: x.split()[2],
                lambda x: int(x),
                False],
  'g_unsat':   ['UNSAT', 
                lambda x: b'runlim' in x and b'result:' in x,
                lambda x: x.split()[2],
                lambda x: int(x),
                False],
  'result':    ['RES', 
                lambda x: b'runlim' in x and b'result:' in x,
                lambda x: x.split()[2],
                lambda x: int(x),
                False],
  'time_real': ['REAL[s]', 
                lambda x: b'runlim' in x and b'real:' in x,
                lambda x: x.split()[2],
                lambda x: float(x),
                False],
  'time_time': ['TIME[s]', 
                lambda x: b'runlim' in x and b'time:' in x,
                lambda x: x.split()[2],
                lambda x: float(x),
                False],
  'space':     ['SPACE[MB]', 
                lambda x: b'runlim' in x and b'space:' in x,
                lambda x: x.split()[2],
                lambda x: float(x),
                False],
#  'opts':      ['OPTIONS', 
#                lambda x: b'runlim' in x and b'argv' in x,
#                err_extract_opts,
#                lambda x: str(x),
#                True] 
}

def format_status(l):
    if 'err' in l:
        return 'err'
    if 'ok' in l:
        return 'ok'
    return "".join(set(l))

TOTALS_FORMAT_ERR = {
  'status':    format_status,
  'g_solved':  lambda l: l.count('ok'),
  'g_total':   lambda l: len(l),
  'g_mem':     lambda l: l.count('mem'),
  'g_time':    lambda l: l.count('time'),
  'g_err':     lambda l: l.count('err'),
  'g_sat':     lambda l: l.count(10),
  'g_unsat':   lambda l: l.count(20),
  'time_real': lambda l: round(sum(l), 1),
  'time_time': lambda l: round(sum(l), 1),
  'space':     lambda l: round(sum(l), 1),
}

# column_name : <colname>, <keyword>, <filter>, [<is_dir_stat>] (optional)
FILTER_OUT = {
  'models_arr':  ['MARR', lambda x: b'[' in x, lambda x: 1, False],
  'models_bvar': ['MVAR', lambda x: b'[' not in x, lambda x: 1, False]
}

assert(set(FILTER_LOG.keys()).isdisjoint(set(FILTER_ERR.keys())))
assert(set(FILTER_LOG.keys()).isdisjoint(set(FILTER_OUT.keys())))
assert(set(FILTER_ERR.keys()).isdisjoint(set(FILTER_OUT.keys())))

FILE_STATS_KEYS = list(k for k, f in FILTER_LOG.items() if not f[4])
FILE_STATS_KEYS.extend(list(k for k, f in FILTER_ERR.items() if not f[4]))
FILE_STATS_KEYS.extend(list(k for k, f in FILTER_OUT.items() if not f[3]))

DIR_STATS_KEYS = list(k for k, f in FILTER_LOG.items() if f[4])
DIR_STATS_KEYS.extend(list(k for k, f in FILTER_ERR.items() if f[4]))

g_dir_stats = {}
g_file_stats = {}
g_total_stats = {}
g_format_stats = TOTALS_FORMAT_ERR

def _filter_data(d, file, filters):
    global g_file_stats, g_dir_stats
    
    dir_stats = dict((k, {}) for k in DIR_STATS_KEYS)
    with open(os.path.join(d, file), 'rb') as infile:
        (f_name, f_ext) = _get_name_and_ext(file)

        if os.stat(os.path.join(d, file)).st_size == 0:
            for k in filters:
                if k not in g_file_stats:
                    g_file_stats[k] = {}
                if d not in g_file_stats[k]:
                    g_file_stats[k][d] = {}
                if f_name not in g_file_stats[k][d]:
                    g_file_stats[k][d][f_name] = None
            return
        
        used_filters = set()
        lines = infile.readlines()
        for line in reversed(lines):
            line = line.strip()

            if len(used_filters) == len(filters):
                break

            for k, v in filters.items():
                assert(len(v) == 5)

                # value already extracted for current file
                if k in used_filters:
                    continue

                f_match = v[1]
                f_val = v[2]
                f_format = v[3]
                
                if k in DIR_STATS_KEYS:
                    if not d in g_dir_stats[k]:
                        val = f_format(f_val(line)) if f_match(line) else None
                        if k not in dir_stats:
                            dir_stats[k] = {}
                        if d not in dir_stats[k]:
                            dir_stats[k][d] = []
                        if val is not None:
                            dir_stats[k][d].append(val)
                # skip columns that are not printed
                else:
                    assert(k in FILE_STATS_KEYS)
                    if f_match(line):
                        val = f_format(f_val(line))
                        used_filters.add(k)
                    else:
                        val = None

                    if k not in g_file_stats:
                        g_file_stats[k] = {}

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

    for k in dir_stats:
        for d in dir_stats[k]:
            if k not in g_dir_stats:
                g_dir_stats[k] = {}
            g_dir_stats[k][d] = dir_stats[k][d]


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
        for d in data[k]:
            for f in g_benchmarks:
                if f not in data[k][d]:
                    data[k][d][f] = None

def _normalize_data(data):
    global g_args, g_dir_stats

    assert('result' in data)
    # reset timeout if given
    if g_args.timeout:
        for d in data['time_time']:
            for f in data['time_time'][d]:
                if data['time_time'][d][f] > g_args.timeout[d]:
                    data['time_time'][d][f] = g_args.timeout[d]
                    data['status'][d][f] = "time"
                    data['result'][d][f] = 1
                    if g_args.g:
                        for k in ["g_total", "g_solved", "g_time",
                                  "g_mem", "g_err"]:
                            g_file_stats[k][d][f] = "time"

    # normalize status ok, time, mem, err
    for k in ['status', 'g_total', 'g_solved', 'g_time', 'g_mem', 'g_err']:
        if k not in data:
            continue
        for d in data[k]:
            for f in data[k][d]:
                if data[k][d][f] == 'ok' \
                   and data['result'][d][f] not in (10, 20):
                    data[k][d][f] = 'err'

    # collect data for virtual best solver
    if g_args.vb:
        if g_args.vbp:
            bdir = g_args.dirs[0]   # base run
            prep_dirs = g_args.dirs[1:] # "preprocessing" runs

            for pdir in prep_dirs:
                vbpdir = "{} + {}".format(_base_dir(bdir), _base_dir(pdir))

                # initialize for virtual best solver
                for k in g_dir_stats.keys():
                    g_dir_stats[k][vbpdir] = []

                for k in data.keys():
                    if vbpdir not in data[k]:
                        data[k][vbpdir] = {}

                for f in g_benchmarks:
                    if data["time_time"][bdir][f] < g_args.timeout[bdir]:
                        time_bdir = data["time_time"][bdir][f]
                    else:
                        time_bdir = g_args.timeout[bdir]

                    if data["time_time"][pdir][f] < g_args.timeout[pdir]:
                        time_pdir = data["time_time"][pdir][f]
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
                        data["time_time"][vbpdir][f] = time_vbp
                        if time_vbp >= g_args.timeout[bdir]:
                            data["status"][vbpdir][f] = "time"
                            data["time_time"][vbpdir][f] = g_args.timeout[bdir]
                            if not g_args.g:
                                data["result"][vbpdir][f] = 1
                    else:
                        for k in data.keys():
                            data[k][vbpdir][f] = data[k][bdir][f]
                g_args.dirs.append(vbpdir)
        else:
            vb_dir = "virtual best solver (portfolio)"

            # initialize for virtual best solver
            for k in g_dir_stats.keys():
                g_dir_stats[k][vb_dir] = []

            for f in g_benchmarks:
                v = sorted(
                    [(data['time_time'][d][f], d) \
                        for d in g_args.dirs \
                            if data['time_time'][d][f] is not None])

                best_dir = v[0][1]
                for k in data.keys():
                    if vb_dir not in data[k]:
                        data[k][vb_dir] = {}
                    data[k][vb_dir][f] = data[k][best_dir][f]
            g_args.dirs.append(vb_dir)


    # add uniquely solved column
    if g_args.u:
        FILE_STATS_KEYS.append('g_uniq')
        g_args.columns.append('g_uniq')
        FILTER_ERR['g_uniq'] = ['UNIQ',
                                lambda x: False,
                                lambda x: None,
                                lambda x: None,
                                False]
        data['g_uniq'] = {}
        for f in g_benchmarks:
            stats = []
            for d in data['status']:
                if d not in data['g_uniq']:
                    data['g_uniq'][d] = {}
                stats.append(data['status'][d][f])
            set_uniq = False
            uniq_exists = stats.count('ok') == 1
            for d in data['status']:
                if uniq_exists and data['status'][d][f] == 'ok':
                    assert (not set_uniq)
                    data['g_uniq'][d][f] = 1
                    set_uniq = True
                else:
                    data['g_uniq'][d][f] = None

def _read_out_file(d, f):
    _filter_data(d, f, FILTER_OUT)

def _save_cache_file(dir):
    global g_file_stats, g_dir_stats

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
    global g_file_stats, g_dir_stats, g_benchmarks

    sum_filename = "{}/cache".format(dir)
    if os.path.isfile(sum_filename):
        with open(sum_filename, "r") as sum_file:
            keys = None
            for line in sum_file:
                # initialize keys
                if keys is None:
                    keys = line.split()

                    expected_keys = list(FILTER_ERR.keys())
                    if not g_parse_err_only:
                        expected_keys.extend(FILTER_LOG.keys())
                        if g_args.m:
                            expected_keys.extend(FILTER_OUT.keys())

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
                        assert(k in FILE_STATS_KEYS)
                        if k not in g_file_stats:
                            g_file_stats[k] = {}
                        if dir not in g_file_stats[k]:
                            g_file_stats[k][dir] = {}
                        if k in FILTER_LOG:
                            t = FILTER_LOG[k]
                        else:
                            assert(k in FILTER_ERR)
                            t = FILTER_ERR[k]
                        assert(len(t) == 5)
                        f_format = t[3] 
                        assert(f not in g_file_stats[k][dir])
                        if data[i] == "None":
                            g_file_stats[k][dir][f] = None
                        else:
                            g_file_stats[k][dir][f] = f_format(data[i])
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

    best_stats = dict((k, {}) for k in FILE_STATS_KEYS)
    diff_stats = dict((k, {}) for k in FILE_STATS_KEYS)

    for f in benchmarks:
        for k in data.keys():
            v = sorted(\
                [(data[k][d][f], d) \
                    for d in g_args.dirs if data[k][d][f] is not None],
                reverse=sort_reverse)

            # strings are not considered for diff/best values
            if len(v) == 0 or isinstance(v[0][0], str):
                best_stats[k][f] = None
                diff_stats[k][f] = None
                continue

            best_dir = v[0][1]

            if len(set([t[0] for t in v])) <= 1:
                best_stats[k][f] = None
            else:
                best_stats[k][f] = best_dir

            if best_stats[k][f] is None or not f_cmp(v[0][0], v[1][0]):
                diff_stats[k][f] = None
            else:
                diff_stats[k][f] = best_dir

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
    if key in FILTER_LOG:
        return FILTER_LOG[key][0]
    elif key in FILTER_ERR:
        return FILTER_ERR[key][0]
    assert(key in FILTER_OUT)
    return FILTER_OUT[key][0]


def _get_color(f, d, diff_stats, best_stats):
    global g_args

    for k in diff_stats.keys():
        if g_args.cmp_col == k:
            if diff_stats[k][f] == d:
                return COLOR_DIFF
            elif best_stats[k][f] == d:
                return COLOR_BEST
    return COLOR_NOCOLOR


def _get_group_totals():
    global g_args, g_benchmarks, g_file_stats, g_format_stats
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

            for stat in g_args.columns:
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
    for stat in g_args.columns:
        assert(stat not in totals)
        totals[stat] = {}
        for d in g_args.dirs:
            if d not in totals[stat]:
                totals[stat][d] = {}

            for group in stats:
                assert(group not in totals[stat][d])
                if stat in g_format_stats:
                    fmt_stat = g_format_stats[stat]
                    val = fmt_stat(stats[group][d][stat])
                else:
                    val = sum(stats[group][d][stat])
                totals[stat][d][group] = val 

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
    global g_file_stats, g_dir_stats

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
                else (COLOR_DISC if ((not g_args.vbsd \
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


if __name__ == "__main__":
    try:
        aparser = ArgumentParser(
                      formatter_class=ArgumentDefaultsHelpFormatter,
                      epilog="availabe values for column: {{ {} }}, " \
                             "note: {{ {} }} are enabled for '-M' only.".format(
                          ", ".join(sorted(FILE_STATS_KEYS)),
                          ", ".join(sorted(list(FILTER_OUT.keys())))))
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
                metavar="column", dest="cmp_col", default='time_time',
                choices=FILE_STATS_KEYS,
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
        g_args = aparser.parse_args()

        # do not use a set here as the order of directories should be preserved
        unique_dirs = []
        for d in g_args.dirs:
            if d not in unique_dirs:
                unique_dirs.append(d)
        g_args.dirs = unique_dirs

        if len(g_args.dirs) < 1:
            raise CmpSMTException ("invalid number of dirs given")

        if g_args.vbp: g_args.vb = True

        for d in g_args.dirs:
            if not os.path.isdir(d):
                raise CmpSMTException ("given smt run is not a directory")

        if g_args.columns is None:
            if g_args.g:
                g_args.columns = \
                    "status,result,g_solved,g_total,g_time,g_mem,g_err," \
                    "time_time,space"
            else:
                g_args.columns = "status,result,time_time,space"
            
        # column options
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
            
        g_args.columns = g_args.columns.split(',')
        for c in g_args.columns:
            if c not in FILE_STATS_KEYS:
                raise CmpSMTException("column '{}' not available".format(c))

        if g_args.show_all:
            g_args.columns = FILE_STATS_KEYS

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
            remove_columns.extend(FILTER_OUT.keys())

        for c in remove_columns:
            if g_args.columns.count(c) > 0:
                g_args.columns.remove(c)

        # disable comparison if cmp_col is not in the columns list
        if g_args.cmp_col not in g_args.columns:
            g_args.cmp_col = None

        if g_args.no_colors:
            COLOR_BEST = ''
            COLOR_DIFF = ''
            COLOR_DISC = ''
            COLOR_STAT = ''
            COLOR_NOCOLOR = ''

        if g_args.timeof and not g_args.timeof in g_args.dirs:
            raise CmpSMTException ("invalid dir given")

        # initialize global data
        g_dir_stats = dict((k, {}) for k in DIR_STATS_KEYS)

        if len(set(g_args.columns).intersection(FILTER_LOG)) == 0:
            g_parse_err_only = True

        _read_data(g_args.dirs)

        # remove files not to display
        if g_args.filter:
            for f in g_benchmarks.copy():
                if g_args.filter not in str(f):
                    g_benchmarks.remove(f)

        if len(g_file_stats.keys()) > 0:
            #assert(len(g_file_stats.keys()) == len(g_args.columns))
            _init_missing_files (g_file_stats)
            _normalize_data(g_file_stats)

            if g_args.g and 'result' in g_args.columns:
                g_args.columns.remove('result')
                del(g_file_stats['result'])
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

