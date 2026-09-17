#!/bin/sh
set -eu
cd "$(dirname "$0")"
mkdir -p tmp/pdfs output/pdf
latexmk -pdf -interaction=nonstopmode -halt-on-error -file-line-error \
  -outdir=tmp/pdfs aoki_cup_powers.tex
cp tmp/pdfs/aoki_cup_powers.pdf output/pdf/aoki_cup_powers.pdf
