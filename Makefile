OPTIONS=--rewriting --irrelevant-projections --without-K --no-default-libraries -W all --warning noUnknownFixityInMixfixDecl --show-implicit
#--exact-split --without-K --proof-irrelevance --verbose=5 --experimental-irrelevance --instance-search-depth=10 --overlapping-instances

all: typecheck

run: build
	./Main

build:
	agda ${OPTIONS} -c Main.agda

typecheck:
	agda ${OPTIONS} Main.agda

test:
	agda ${OPTIONS} Test.agda

classic:
	cd Mathematical && agda ${OPTIONS} --cubical --prop Main.agda

docs:
	agda ${OPTIONS} --html Main.agda

clean:
	find . -type f -name '*.agdai' -delete
