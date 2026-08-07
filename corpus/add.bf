Modular addition: reads two cells a and b from input and prints one
cell holding their sum with wrapping arithmetic

Tape layout uses two cells:
  cell0 holds a and becomes the accumulator
  cell1 holds b and is counted down to zero

read a into cell0 and b into cell1
,>,

while b is nonzero move one unit from b to a
[-<+>]

step back onto the accumulator and print it
<.
