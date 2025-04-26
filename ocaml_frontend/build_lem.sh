#!/usr/bin/env bash

lem -wl ign \
    -wl_rename warn \
    -wl_pat_red err \
    -wl_pat_exh warn \
    -ocaml "$@" 2> lem.log || \
    (>&2 cat lem.log; exit 1)
