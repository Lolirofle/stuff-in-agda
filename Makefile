OPTIONS=--rewriting
#--exact-split --without-K

all: typecheck

run: build
	./Main

build:
	agda ${OPTIONS} -c Main.agda

typecheck:
	agda ${OPTIONS} Main.agda

test:
	agda ${OPTIONS} Test.agda
