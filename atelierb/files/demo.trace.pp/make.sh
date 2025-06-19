#!/bin/bash

krt=             # set to the path of krt binary
pp_kin=          # set to PP's bytecode (PP.kin)
replay_kin=      # set to REPLAY's bytecode (REPLAY.kin)

rm pp.res pp.trace replay.res replay.trace
${krt} -b ${pp_kin} pp.goal
${krt} -b ${replay_kin} replay.goal > replay.trace

