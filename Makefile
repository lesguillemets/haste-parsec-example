./build/calc.js: ./src/*.hs
	hastec -O2 ./src/Calc.hs -isrc -o ./build/calc.js --opt-all
