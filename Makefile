OPTIONS=--rewriting --without-K --no-default-libraries --no-libraries --no-guardedness --no-sized-types --no-import-sorts --no-print-pattern-synonyms --exact-split
DEBUG_OPTIONS=--show-implicit --confluence-check -W all --warning noUnknownFixityInMixfixDecl --cubical
#--cubical --exact-split --proof-irrelevance --verbose=5 --experimental-irrelevance --instance-search-depth=10 --overlapping-instances

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

classic:
	cd Mathematical && agda ${OPTIONS} --cubical --prop All.agda

docs:
	agda ${OPTIONS} --html --html-dir=gen/html All.agda

clean:
	find . -type f -name '*.agdai' -delete

generate:
	env python3 generate_All.agda.py > All.agda
