OPTIONS=--rewriting
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
	agda ${OPTIONS} MainClassic.agda
