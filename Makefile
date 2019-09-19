RESULT = homusat
# YFLAGS = -v
OCAMLLDFLAGS = -warn-error -31
LIBS = unix
default: native-code
# OCAMLC = ocamlcp
# OCAMLOPT = ocamloptp
# OCAMLFLAGS = -P -fim

SOURCES = \
x.ml \
flags.ml \
log.mli log.ml \
profile.mli profile.ml \
position.mli position.ml \
id.mli id.ml \
LTS.mli LTS.ml \
HES.mli HES.ml \
parser.mly lexer.mll \
alphaHES.mli alphaHES.ml \
typing.mli typing.ml \
HFS.mli HFS.ml \
alphaHFS.mli alphaHFS.ml \
norm.mli norm.ml \
preproc.mli preproc.ml \
reduction.mli reduction.ml \
analysis.mli analysis.ml \
enc.mli enc.ml \
ACG.mli ACG.ml \
flow.mli flow.ml \
dependency.mli dependency.ml \
types.mli types.ml \
AMS.mli AMS.ml \
opt.mli opt.ml \
typeJudge.mli typeJudge.ml \
typeCheck.mli typeCheck.ml \
imm.mli imm.ml \
saturation.mli saturation.ml \
graph.mli graph.ml \
solver.mli solver.ml \
main.ml

include OCamlMakefile
