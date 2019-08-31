OPTIONS=--rewriting --irrelevant-projections --without-K --no-default-libraries --show-implicit
#--exact-split --without-K --proof-irrelevance --verbose=5

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
	agda ${OPTIONS} --prop MainClassic.agda

docs:
	agda ${OPTIONS} --html Main.agda

clean:
	find . -type f -name '*.agdai' -delete
