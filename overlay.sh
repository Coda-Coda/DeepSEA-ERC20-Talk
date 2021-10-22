#!/usr/bin/env sh
# The video has the wrong inequality; fix that by overlaying.

# Figure out range of frames
# ffmpeg -i alectryon.typo.mp4 -vf "drawtext=fontfile=Arial.ttf: text=%{n}: x=(w-tw)/2: y=h-(2*lh): fontcolor=white: box=1: boxcolor=0x00000099" -y alectryon.fnum.mp4
# [533-718]

ffmpeg -i alectryon.typo.mp4 -i overlay.png -filter_complex "overlay=0:0:enable='between(n,533,718)'" -c:a copy alectryon.mp4
