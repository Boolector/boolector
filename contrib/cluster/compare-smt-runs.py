#! /usr/bin/env python3

from argparse import ArgumentParser, REMAINDER
import os
import sys

class CmpSMTException (Exception):
    def __init__ (self, msg):
        self.msg = msg
    def __str__ (self):
        return "[cmpsmt] Error: {0:s}".format(self.msg)

g_args = None

g_files = {}
g_idx = 0

g_run_lods = {}
g_run_satcalls = {}
g_run_time_sat = {}
g_run_time_rw = {}
g_run_time_beta = {}
g_run_time_eval = {}
g_run_time_app = {}
g_run_time_clapp = {}
g_run_time_sapp = {}

g_run_status = {}
g_run_result = {}
g_run_real = {}
g_run_time = {}
g_run_space = {}

g_run_opts = {}

g_best_run_lods = {}
g_best_run_satcalls = {}
g_best_run_time_sat = {}
g_best_run_time_rw = {}
g_best_run_time_beta = {}
g_best_run_time_eval = {}
g_best_run_time_app = {}
g_best_run_time_clapp = {}
g_best_run_time_sapp = {}

g_best_run_status = {}
g_best_run_result = {}
g_best_run_real = {}
g_best_run_time = {}
g_best_run_space = {}

g_best_diff_run_lods = {}
g_best_diff_run_satcalls = {}
g_best_diff_run_time_sat = {}
g_best_diff_run_time_rw = {}
g_best_diff_run_time_beta = {}
g_best_diff_run_time_eval = {}
g_best_diff_run_time_app = {}
g_best_diff_run_time_clapp = {}
g_best_diff_run_time_sapp = {}

g_best_diff_run_status = {}
g_best_diff_run_result = {}
g_best_diff_run_real = {}
g_best_diff_run_time = {}
g_best_diff_run_space = {}

COLOR_BEST = '\033[36m'
COLOR_DIFF = '\033[32m'
COLOR_DISC = '\033[31m'
COLOR_STAT = '\033[33m'
COLOR_NOCOLOR = '\033[0m'

def _get_name_and_ext (filename):
    return ("".join(filename.rpartition('.')[:-2]), filename.rpartition('.')[-1])

def _read_log_file (d, f):
    global g_run_lods, g_run_satcalls, g_run_time_sat, g_run_time_rw
    global g_run_time_beta, g_run_time_eval
    global g_run_time_sapp, g_run_time_clapp, g_run_time_app
    with open(os.path.join(d, f), 'rb') as infile:
        for line in infile:
            idx = g_files[_get_name_and_ext(f)[0]]
            if d not in g_run_lods:
                g_run_lods[d] = {}
            if d not in g_run_satcalls:
                g_run_satcalls[d] = {}
            if d not in g_run_time_sat:
                g_run_time_sat[d] = {}
            if d not in g_run_time_rw:
                g_run_time_rw[d] = {}
            if d not in g_run_time_beta:
                g_run_time_beta[d] = {}
            if d not in g_run_time_eval:
                g_run_time_eval[d] = {}
            if d not in g_run_time_clapp:
                g_run_time_clapp[d] = {}
            if d not in g_run_time_sapp:
                g_run_time_sapp[d] = {}
            if d not in g_run_time_app:
                g_run_time_app[d] = {}
            if b'LOD' in line:
                g_run_lods[d][idx] = int(line.split()[3])
            elif b'SAT calls' in line:
                g_run_satcalls[d][idx] = int(line.split()[1])
            elif b'pure SAT' in line:
                g_run_time_sat[d][idx] = float(line.split()[1])
            elif b'rewriting engine' in line:
                g_run_time_rw[d][idx] = float(line.split()[1])
            elif b'beta-reduction' in line:
                g_run_time_beta[d][idx] = float(line.split()[1])
            elif b'seconds expression evaluation' in line:
                g_run_time_eval[d][idx] = float(line.split()[1])
            elif b'cloning for initial applies search' in line:
                g_run_time_clapp[d][idx] = float(line.split()[1])
            elif b'SAT solving for initial applies search' in line:
                g_run_time_sapp[d][idx] = float(line.split()[1])
            elif b'initial applies search' in line:
                g_run_time_app[d][idx] = float(line.split()[1])


def _read_err_file (d, f):
    global g_run_status, g_run_result, g_run_real, g_run_time, g_run_space
    with open(os.path.join(d, f), 'rb') as infile:
        idx = g_files[_get_name_and_ext(f)[0]]
        g_run_opts[d] = []
        for line in infile:
            if b'status:' in line:
                if d not in g_run_status:
                    g_run_status[d] = {}
                status = line.split()[2:]
                if status[0] == b'ok':
                    g_run_status[d][idx] = "ok"
                elif status[0] == b'out':
                    if status[-1] == b'time':
                        g_run_status[d][idx] = "time"
                    elif status[-1] == b'memory':
                        g_run_status[d][idx] = "mem"
                    else:
                        raise CmpSMTException(
                                "invalid status in run '{}'".format(f))
                else:
                    raise CmpSMTException(
                            "invalid status in run '{}'".format(f))
            elif b'result:' in line:
                if d not in g_run_result:
                    g_run_result[d] = {}
                g_run_result[d][idx] = int(line.split()[2])
            elif b'real:' in line:
                if d not in g_run_real:
                    g_run_real[d] = {}
                g_run_real[d][idx] = float(line.split()[2])
            elif b'time:' in line:
                if d not in g_run_time:
                    g_run_time[d] = {}
                g_run_time[d][idx] = float(line.split()[2])
            elif b'space:' in line:
                if d not in g_run_space:
                    g_run_space[d] = {}
                g_run_space[d][idx] = float(line.split()[2])
            elif b'argv' in line:
                opt = str(line.split()[2])
                if opt[2] == '-':
                    g_run_opts[d].append(opt[2:-1])
    if g_run_status[d][idx] == "ok" \
       and g_run_result[d][idx] != 10 and g_run_result[d][idx] != 20:
            g_run_status[d][idx] = "err"

def _read_data (dirs):
    global g_files, g_idx
    for d in dirs:
        init_files = g_idx == 0
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
                    # init g_files
                    if init_files:
                        g_files[f_name] = g_idx
                        g_idx += 1
                    # init data
                    if not g_args.filter or g_args.filter in str(f):
                        _read_log_file (d, f)
                        _read_err_file (d, "{}{}".format(f[:-3], "err"))


def _pick_data ():                        
    global g_best_run_lods, g_best_run_satcalls, g_best_run_time_sat
    global g_best_run_time_rw, g_best_run_time_beta, g_best_run_time_eval
    global g_best_run_time_app, g_best_run_time_clapp
    global g_best_run_time_sapp
    global g_best_run_status, g_best_run_result, g_best_run_real
    global g_best_run_time, g_best_run_space
    global g_best_diff_run_lods, g_best_diff_run_satcalls
    global g_best_diff_run_time_sat, g_best_diff_run_time_rw
    global g_best_diff_run_time_beta, g_best_diff_run_time_eval
    global g_best_diff_run_time_app, g_best_diff_run_clapp
    global g_best_diff_run_sapp
    global g_best_diff_run_status, g_best_diff_run_result, g_best_diff_run_real
    global g_best_diff_run_time, g_best_diff_run_space
    
    for f in g_files:
        try:
            v = [(g_run_real[d][g_files[f]], d) for d in g_args.dirs]
            v = sorted(v)
            g_best_run_real[f] = None \
                    if len(set(iter([t[0] for t in v]))) <= 1  \
                    or g_run_status[d][g_files[f]] == 'time' else v[0][1]
            g_best_diff_run_real[f] = None \
                    if not g_best_run_real[f] \
                       or v[0][0] + g_args.diff > v[1][0] \
                    else v[0][1]
        except KeyError:
            g_best_run_real[f] = None
            g_best_diff_run_real[f] = None
        try:
            v = [(g_run_time[d][g_files[f]], d) for d in g_args.dirs]
            v = sorted(v)
            g_best_run_time[f] = None \
                    if len(set(iter([t[0] for t in v]))) <= 1 \
                    or g_run_status[d][g_files[f]] == 'time'  else v[0][1]
            g_best_diff_run_time[f] = None \
                    if not g_best_run_time[f] \
                       or v[0][0] + g_args.diff > v[1][0] \
                    else v[0][1]
        except KeyError:
            g_best_run_time[f] = None
            g_best_diff_run_time[f] = None
        try:
            v = [(g_run_space[d][g_files[f]], d) for d in g_args.dirs]
            v = sorted(v)
            g_best_run_space[f] = None \
                    if len(set(iter([t[0] for t in v]))) <= 1 \
                    or g_run_status[d][g_files[f]] == 'time'  else v[0][1]
            g_best_diff_run_space[f] = None \
                    if not g_best_run_space[f] \
                       or v[0][0] + g_args.diff > v[1][0] \
                    else v[0][1]
        except KeyError:
            g_best_run_space[f] = None
            g_best_diff_run_space[f] = None
        try:
            v = [(g_run_lods[d][g_files[f]], d) for d in g_args.dirs]
            v = sorted(v)
            g_best_run_lods[f] = None \
                    if len(set(iter([t[0] for t in v]))) <= 1 \
                    or g_run_status[d][g_files[f]] == 'time'  else v[0][1]
            g_best_diff_run_lods[f] = None \
                    if not g_best_run_lods[f] \
                       or v[0][0] + g_args.diff > v[1][0] \
                    else v[0][1]
        except KeyError:
            g_best_run_lods[f] = None
            g_best_diff_run_lods[f] = None
        try:
            v = [(g_run_satcalls[d][g_files[f]], d) for d in g_args.dirs]
            v = sorted(v)
            g_best_run_satcalls[f] = None \
                    if len(set(iter([t[0] for t in v]))) <= 1 \
                    or g_run_status[d][g_files[f]] == 'time'  else v[0][1]
            g_best_diff_run_satcalls[f] = None \
                    if not g_best_run_satcalls[f] \
                       or v[0][0] + g_args.diff > v[1][0] \
                    else v[0][1]
        except KeyError:
            g_best_run_satcalls[f] = None
            g_best_diff_run_satcalls[f] = None
        try:
            v = [(g_run_time_sat[d][g_files[f]], d) for d in g_args.dirs]
            v = sorted(v)
            g_best_run_time_sat[f] = None \
                    if len(set(iter([t[0] for t in v]))) <= 1 \
                    or g_run_status[d][g_files[f]] == 'time' else v[0][1]
            g_best_diff_run_time_sat[f] = None \
                    if not g_best_run_time_sat[f] \
                       or v[0][0] + g_args.diff > v[1][0] \
                    else v[0][1]
        except KeyError:
            g_best_run_time_sat[f] = None
            g_best_diff_run_time_sat[f] = None
        try:
            v = [(g_run_time_rw[d][g_files[f]], d) for d in g_args.dirs]
            v = sorted(v)
            g_best_run_time_rw[f] = None \
                    if len(set(iter([t[0] for t in v]))) <= 1 \
                    or g_run_status[d][g_files[f]] == 'time'  else v[0][1]
            g_best_diff_run_time_rw[f] = None \
                    if not g_best_run_time_rw[f] \
                       or v[0][0] + g_args.diff > v[1][0] \
                    else v[0][1]
        except KeyError:
            g_best_run_time_rw[f] = None
            g_best_diff_run_time_rw[f] = None
        try:
            v = [(g_run_time_beta[d][g_files[f]], d) for d in g_args.dirs]
            v = sorted(v)
            g_best_run_time_beta[f] = None \
                    if len(set(iter([t[0] for t in v]))) <= 1 \
                    or g_run_status[d][g_files[f]] == 'time'  else v[0][1]
            g_best_diff_run_time_beta[f] = None \
                    if not g_best_run_time_beta[f] \
                       or v[0][0] + g_args.diff > v[1][0] \
                    else v[0][1]
        except KeyError:
            g_best_run_time_beta[f] = None
            g_best_diff_run_time_beta[f] = None
        try:
            v = [(g_run_time_eval[d][g_files[f]], d) for d in g_args.dirs]
            v = sorted(v)
            g_best_run_time_eval[f] = None \
                    if len(set(iter([t[0] for t in v]))) <= 1 \
                    or g_run_status[d][g_files[f]] == 'time'  else v[0][1]
            g_best_diff_run_time_eval[f] = None \
                    if not g_best_run_time_eval[f] \
                       or v[0][0] + g_args.diff > v[1][0] \
                    else v[0][1]
        except KeyError:
            g_best_run_time_eval[f] = None
            g_best_diff_run_time_eval[f] = None
        try:
            v = [(g_run_time_app[d][g_files[f]], d) for d in g_args.dirs]
            v = sorted(v)
            g_best_run_time_app[f] = None \
                    if len(set(iter([t[0] for t in v]))) <= 1 else v[0][1]
            g_best_diff_run_time_app[f] = None \
                    if not g_best_run_time_app[f] \
                       or v[0][0] + g_args.diff > v[1][0] \
                    else v[0][1]
        except KeyError:
            g_best_run_time_app[f] = None
            g_best_diff_run_time_app[f] = None
        try:
            v = [(g_run_time_clapp[d][g_files[f]], d) \
                    for d in g_args.dirs]
            v = sorted(v)
            g_best_run_time_clapp[f] = None \
                    if len(set(iter([t[0] for t in v]))) <= 1 else v[0][1]
            g_best_diff_run_time_clapp[f] = None \
                    if not g_best_run_time_clapp[f] \
                       or v[0][0] + g_args.diff > v[1][0] \
                    else v[0][1]
        except KeyError:
            g_best_run_time_clapp[f] = None
            g_best_diff_run_time_clapp[f] = None
        try:
            v = [(g_run_time_sapp[d][g_files[f]], d) \
                    for d in g_args.dirs]
            v = sorted(v)
            g_best_run_time_sapp[f] = None \
                    if len(set(iter([t[0] for t in v]))) <= 1 else v[0][1]
            g_best_diff_run_time_sapp[f] = None \
                    if not g_best_run_time_sapp[f] \
                       or v[0][0] + g_args.diff > v[1][0] \
                    else v[0][1]
        except KeyError:
            g_best_run_time_sapp[f] = None
            g_best_diff_run_time_sapp[f] = None

        
def _print_data ():
    padding = 1
    name_col_width = padding + max(len(f) for f in g_files)
    data_col_width = {}
    stat_col_width = padding + len("STAT") 
    res_col_width = padding + len("RESULT")
    real_col_width = {}
    time_col_width = {}
    space_col_width = {}
    lods_col_width = {}
    calls_col_width = {}
    sat_col_width = {}
    rw_col_width = {}
    beta_col_width = {}
    app_col_width = {}
    clapp_col_width = {}
    sapp_col_width = {}
    data_col_width = {}
    for d in g_args.dirs:
        real_col_width[d] = padding + max(len("REAL[s]"),
                max(len(str(item[1])) for item in g_run_real[d].items()))
        time_col_width[d] = padding + max(len("TIME[s]"),
                max(len(str(item[1])) for item in g_run_time[d].items()))
        space_col_width[d] = padding + max(len("SPACE[s]"),
                max(len(str(item[1])) for item in g_run_space[d].items()))
        lods_col_width[d] = padding + max(len("LODS"),
                max(len(str(item[1])) for item in g_run_lods[d].items()))
        calls_col_width[d] = padding + max(len("CALLS"),
                max(len(str(item[1])) for item in g_run_satcalls[d].items()))
        sat_col_width[d] = padding + max(len("SAT[s]"),
                max(len(str(item[1])) for item in g_run_time_sat[d].items()))
        rw_col_width[d] = padding + max(len("RW[s]"),
                max(len(str(item[1])) for item in g_run_time_rw[d].items()))
        beta_col_width[d] = padding + max(len("BETA[s]"),
                max(len(str(item[1])) for item in g_run_time_beta[d].items()))
        app_col_width[d] = padding + max(len("APP[s]"),
                max(len(str(item[1])) for item in g_run_time_app[d].items()))
        clapp_col_width[d] = padding + (max(len("CLONE[s]"),
                max(len(str(item[1])) for item in g_run_time_clapp[d].items())) \
                        if len(g_run_time_clapp[d]) else len("CLONE[s]"))
        sapp_col_width[d] = padding + (max(len("SAT[s]"),
                max(len(str(item[1])) for item in g_run_time_sapp[d].items())) \
                        if len(g_run_time_sapp[d]) else len("SAT[s]"))
        data_col_width[d] = stat_col_width \
                            + lods_col_width[d] + calls_col_width[d] \
                            + sat_col_width[d] + rw_col_width[d] \
                            + beta_col_width[d] \
                            if g_args.bs \
                            else \
                                (stat_col_width + time_col_width[d] \
                                 + app_col_width[d] + clapp_col_width[d] \
                                 + sapp_col_width[d] \
                                 if g_args.dp else \
                                 stat_col_width + res_col_width \
                                 + real_col_width[d] + time_col_width[d] \
                                 + space_col_width[d])
    
    print ("{} | {} |".format (
        "DIRECTORY".rjust(name_col_width),
        " | ".join(d.center(max(data_col_width[d], len(d))) 
            for d in g_args.dirs)))

    print ("{} | {} |\n".format (
        "OPTIONS".rjust(name_col_width),
        " | ".join(" ".join(opt for opt in g_run_opts[d]).center(
                max(data_col_width[d], len(d)))
            for d in g_args.dirs))) 

    if g_args.bs:
        print ("{} | {} |\n".format (
            "".rjust(name_col_width),
            " | ".join("{}".format (
                "BOOLECTOR STATS".center(data_col_width[d]))
                for d in g_args.dirs)))
        print ("{} | {} |".format (
            "BENCHMARK".rjust(name_col_width),
            " | ".join("{}{}{}{}{}{}".format (
                "STAT".rjust(stat_col_width),
                "LODS".rjust(lods_col_width[d]),
                "CALLS".rjust(calls_col_width[d]),
                "SAT[s]".rjust(sat_col_width[d]),
                "RW[s]".rjust(rw_col_width[d]),
                "BETA[s]".rjust(beta_col_width[d]))
                for d in g_args.dirs)))
    elif g_args.dp:
        print ("{} | {} |\n".format (
            "".rjust(name_col_width),
            " | ".join("{}".format (
                "DUAL PROP STATS".center(data_col_width[d]))
                for d in g_args.dirs)))
        print ("{} | {} |".format (
            "BENCHMARK".rjust(name_col_width),
            " | ".join("{}{}{}{}{}".format (
                "STAT".rjust(stat_col_width),
                "TIME[s]".rjust(time_col_width[d]),
                "APP[s]".rjust(app_col_width[d]),
                "CLONE[s]".rjust(clapp_col_width[d]),
                "SAT[s]".rjust(sapp_col_width[d])) 
                for d in g_args.dirs)))
    else:
        print ("{} | {} |".format (
            "BENCHMARK".rjust(name_col_width),
            " | ".join("{}{}{}{}{}".format (
                "STAT".rjust(stat_col_width),
                "RESULT".rjust(res_col_width),
                "REAL[s]".rjust(real_col_width[d]),
                "TIME[s]".rjust(time_col_width[d]),
                "SPACE[s]".rjust(space_col_width[d])) 
                for d in g_args.dirs)))

    for f in sorted(g_files.keys()):
        if g_args.t \
           and len(set(
               [g_run_status[d][g_files[f]] 
                for d in g_args.dirs
                if g_run_status[d][g_files[f]] == "time"])) < 1:
            continue

        if g_args.e \
           and len(set(
               [g_run_status[d][g_files[f]] 
                for d in g_args.dirs
                if g_run_status[d][g_files[f]] == "err"])) < 1:
            continue
        if g_args.o \
           and len(set(
               [g_run_status[d][g_files[f]] 
                for d in g_args.dirs
                if g_run_status[d][g_files[f]] != "ok"])) >= 1:
            continue

        idx = g_files[f]
        s = [g_run_status[d][g_files[f]] for d in g_args.dirs]
        r = [g_run_result[d][g_files[f]] for d in g_args.dirs]
        color = COLOR_STAT \
                if len(set(iter(s))) > 1 \
                else (COLOR_DISC if len(set(iter(r))) > 1 \
                                 else COLOR_NOCOLOR)
        if g_args.bs:
            print ("{}{} | {} |{}".format (
                color,
                f.rjust(name_col_width),
                " | ".join("{}{}{}{}{}{}{}{}".format (
                    color \
                        if color != COLOR_NOCOLOR \
                        else (\
                            COLOR_DIFF
                            if (g_best_diff_run_lods[f]
                                and g_best_diff_run_lods[f] == d
                                and g_args.cmp_col == "lods")
                               or (g_best_diff_run_satcalls[f] 
                                   and g_best_diff_run_satcalls[f] == d 
                                   and g_args.cmp_col == "calls") \
                               or (g_best_run_time_sat[f]
                                   and g_best_run_time_sat[f] == d
                                   and g_args.cmp_col == "sat") \
                               or (g_best_run_time_rw[f]
                                   and g_best_run_time_rw[f] == d
                                   and g_args.cmp_col == "rw") \
                               or (g_best_diff_run_time_beta[f]
                                   and g_best_diff_run_time_beta[f] == d
                                   and g_args.cmp_col == "beta") \
                            else ( \
                                COLOR_BEST \
                                if (g_best_run_lods[f]
                                    and g_best_run_lods[f] == d
                                    and g_args.cmp_col == "lods") \
                                   or (g_best_run_satcalls[f] 
                                       and g_best_run_satcalls[f] == d
                                       and g_args.cmp_col == "calls") \
                                   or (g_best_run_time_sat[f]
                                       and g_best_run_time_sat[f] == d
                                       and g_args.cmp_col == "sat") \
                                   or (g_best_run_time_rw[f]
                                       and g_best_run_time_rw[f] == d
                                       and g_args.cmp_col == "rw") \
                                   or (g_best_run_time_beta[f]
                                       and g_best_run_time_beta[f] == d
                                       and g_args.cmp_col == "beta")
                                else COLOR_NOCOLOR)),
                    g_run_status[d][idx].rjust(stat_col_width),
                    str(g_run_lods[d][idx]).rjust(lods_col_width[d]) \
                            if idx in g_run_lods[d] \
                            else " - ".rjust(lods_col_width[d]),
                    str(g_run_satcalls[d][idx]).rjust(calls_col_width[d]) \
                            if idx in g_run_satcalls[d] \
                            else "-".rjust(calls_col_width[d]),
                    str(g_run_time_sat[d][idx]).rjust(sat_col_width[d]) \
                            if idx in g_run_time_sat[d] \
                            else "-".rjust(sat_col_width[d]),
                    str(g_run_time_rw[d][idx]).rjust(rw_col_width[d]) \
                            if idx in g_run_time_rw[d] \
                            else "-".rjust(rw_col_width[d]),
                    str(g_run_time_beta[d][idx]).rjust(beta_col_width[d]) \
                            if idx in g_run_time_beta[d] \
                            else "-".rjust(beta_col_width[d]),
                    color if color != COLOR_NOCOLOR else COLOR_NOCOLOR) \
                    for d in g_args.dirs),
                    COLOR_NOCOLOR))
        elif g_args.dp:
            print ("{}{} | {} |{}".format (
                color,
                f.rjust(name_col_width),
                " | ".join("{}{}{}{}{}{}{}".format (
                    color \
                        if color != COLOR_NOCOLOR \
                        else (\
                            COLOR_DIFF
                            if (g_best_diff_run_time[f]
                                and g_best_diff_run_time[f] == d
                                and g_args.cmp_col == "time")
                               or (g_best_diff_run_time_app[f] 
                                   and g_best_diff_run_time_app[f] == d 
                                   and g_args.cmp_col == "app") \
                               or (g_best_diff_run_time_clapp[f]
                                   and g_best_diff_run_time_clapp[f] == d \
                                   and g_args.cmp_col == "clone") \
                               or (g_best_diff_run_time_sapp[f]
                                   and g_best_diff_run_time_sapp[f] == d 
                                   and g_args.cmp_col == "sat") \
                            else ( \
                                COLOR_BEST \
                                if (g_best_run_time[f]
                                    and g_best_run_time[f] == d
                                    and g_args.cmp_col == "time") \
                                   or (g_best_run_time_app[f] 
                                       and g_best_run_time_app[f] == d
                                       and g_args.cmp_col == "app") \
                                   or (g_best_run_time_clapp[f]
                                       and g_best_run_time_clapp[f] == d
                                       and g_args.cmp_col == "clone") \
                                   or (g_best_run_time_sapp[f]
                                       and g_best_run_time_sapp[f] == d
                                       and g_args.cmp_col == "sat") \
                                else COLOR_NOCOLOR)),
                    g_run_status[d][idx].rjust(stat_col_width),
                    str(g_run_time[d][idx]).rjust(time_col_width[d]) \
                            if idx in g_run_time[d] \
                            else " - ".rjust(time_col_width[d]),
                    str(g_run_time_app[d][idx]).rjust(app_col_width[d]) \
                            if idx in g_run_time_app[d] \
                            else "-".rjust(app_col_width[d]),
                    str(g_run_time_clapp[d][idx]).rjust(clapp_col_width[d]) \
                            if idx in g_run_time_clapp[d] \
                            else "-".rjust(clapp_col_width[d]),
                    str(g_run_time_sapp[d][idx]).rjust(sapp_col_width[d]) \
                            if idx in g_run_time_sapp[d] \
                            else "-".rjust(sapp_col_width[d]),
                    color if color != COLOR_NOCOLOR else COLOR_NOCOLOR) \
                    for d in g_args.dirs),
                    COLOR_NOCOLOR))
        else:
            print ("{}{} | {} |{}".format (
                color,
                f.rjust(name_col_width),
                " | ".join("{}{}{}{}{}{}{}".format (
                    color \
                        if color != COLOR_NOCOLOR \
                        else (\
                            COLOR_DIFF \
                            if (g_best_diff_run_real[f] != None
                                and g_best_diff_run_real[f] == d
                                and g_args.cmp_col == "real") \
                               or (g_best_diff_run_time[f]
                                   and g_best_diff_run_time[f] == d
                                   and g_args.cmp_col == "time") \
                               or (g_best_diff_run_space[f]
                                   and g_best_diff_run_space[f] == d
                                   and g_args.cmp_col == "space") \
                            else ( \
                                COLOR_BEST \
                                if (g_best_run_real[f] != None
                                    and g_best_run_real[f] == d
                                    and g_args.cmp_col == "real") \
                                   or (g_best_run_time[f]
                                       and g_best_run_time[f] == d
                                       and g_args.cmp_col == "time") \
                                   or (g_best_run_space[f]
                                       and g_best_run_space[f] == d
                                       and g_args.cmp_col == "space") \
                                else COLOR_NOCOLOR)),
                    g_run_status[d][idx].rjust(stat_col_width),
                    str(g_run_result[d][idx]).rjust(res_col_width),
                    str(g_run_real[d][idx]).rjust(real_col_width[d]),
                    str(g_run_time[d][idx]).rjust(time_col_width[d]),
                    str(g_run_space[d][idx]).rjust(space_col_width[d]),
                    color if color != COLOR_NOCOLOR else COLOR_NOCOLOR) \
                    for d in g_args.dirs),
                    COLOR_NOCOLOR))



if __name__ == "__main__":
    try:
        aparser = ArgumentParser ()
        aparser.add_argument ("-f", metavar="string", dest="filter", type=str, 
                default=None,
                help="filter benchmark files by <string>")
        aparser.add_argument ("-hd", metavar="seconds", dest="diff", type=int,
                default=5,
                help="highlight time diff > <seconds> (default: 5)")
        aparser.add_argument ("-bs", action="store_true",
                help="compare boolector statistics")
        aparser.add_argument ("-dp", action="store_true",
                help = "compare dual prop statistics")
        aparser.add_argument ("-t", action="store_true",
                help="show timeouts only")
        aparser.add_argument ("-m", action="store_true",
                help="show memory outs only")
        aparser.add_argument ("-e", action="store_true",
                help="show errors only")
        aparser.add_argument ("-o", action="store_true",
                help="show non-errors only")
        aparser.add_argument ("-c", metavar="string", dest="cmp_col", 
                default=None,
                help="compare by column <string> (default: TIME, LODS if -bs)")
        aparser.add_argument ("dirs", nargs=REMAINDER,
                help="two or more smt run directories to compare")
        g_args = aparser.parse_args()

        if len(g_args.dirs) < 2:
            raise CmpSMTException ("invalid number of dirs given")

        for d in g_args.dirs:
            if not os.path.isdir(d):
                raise CmpSMTException ("given smt run is not a directory")

        if not g_args.cmp_col:
            g_args.cmp_col = "lods" if g_args.bs else "time"
        else:
            g_args.cmp_col = g_args.cmp_col.lower()

        _read_data (g_args.dirs)
        _pick_data ()
        _print_data ()

    except KeyboardInterrupt as e:
        sys.exit ("[cmpsmt] interrupted")
    except CmpSMTException as e:
        sys.exit (str(e))

