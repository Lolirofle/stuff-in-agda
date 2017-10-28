all: typecheck

run: build
	./Main

build:
	agda -c Main.agda

typecheck:
	agda Main.agda

test:
	agda Test.agda
