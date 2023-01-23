#!/usr/bin/env python3

from os.path import realpath
import sys

import hovercraft
sys.path.insert(1, './alectryon')
import alectryon.docutils
alectryon.docutils.setup()

from alectryon.serapi import SerAPI
SerAPI.DEFAULT_PP_ARGS["pp_margin"] = 70

from hovercraft.parse import SlideMaker

# Hovercraft's MathJax is outdated and competes with ours
SlideMaker.start_math = SlideMaker.default_start
SlideMaker.start_math_block = SlideMaker.default_start

from hovercraft import position
position.DEFAULT_MOVEMENT = 2600 # Must be > 1920

if __name__ == "__main__":
    hovercraft.main(sys.argv[1:])
