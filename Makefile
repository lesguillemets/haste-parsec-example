./build/calc.js: ./src/*.hs
	hastec --debug --preserve-names ./src/Calc.hs -isrc -o ./build/calc.js
