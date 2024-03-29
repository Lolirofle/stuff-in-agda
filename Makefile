OPTIONS=--rewriting --without-K --no-default-libraries --no-libraries --no-guardedness --no-sized-types --no-import-sorts --no-print-pattern-synonyms --exact-split
DEBUG_OPTIONS=--show-implicit --confluence-check -W all --warning noUnknownFixityInMixfixDecl
# --cubical --proof-irrelevance --verbose=5 --experimental-irrelevance --instance-search-depth=10 --overlapping-instances --no-qualified-instances  --erase-record-parameters --cubical-compatible

all: typecheck

run: build
	./gen/Main

build:
	agda ${OPTIONS} -c --compile-dir=gen Main.agda

js:
	agda ${OPTIONS} --js --js-optimize --compile-dir=gen/Js Js.agda

typecheck: generate
	agda ${OPTIONS} All.agda

debug:
	agda ${OPTIONS} ${DEBUG_OPTIONS} All.agda

test:
	agda ${OPTIONS} Test.agda

dependency-graph:
	agda ${OPTIONS} --dependency-graph=All.dependency-graph.dot All.agda
	dot -Goverlap=scale All.dependency-graph.dot -o All.dependency-graph.svg -Tsvg -GK=10.9 -Gsplines=false -Ksfdp -Ecolor=lightgray -Nshape=box -Nstyle=rounded

classic:
	cd Mathematical && agda ${OPTIONS} --cubical --prop All.agda

docs:
	agda ${OPTIONS} --html --html-dir=gen/html All.agda

clean:
	find . -type f -name '*.agdai' -delete

generate:
	env python3 generate_All.agda.py > All.agda
