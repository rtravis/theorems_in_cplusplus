CXX = g++-9


theorem: theorem.cpp
	$(CXX) -fconcepts -std=c++2a -o theorem theorem.cpp

all: theorem

clean:
	rm -f ./theorem ./a.out

.PHONY: all clean
