//ATOM
// RUN: %dafny /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// Spec# and Boogie and Chalice: The program will be
// the same, except that these languages do not check
// for any kind of termination. Also, in Spec#, there
// is an issue of potential overflows.

// Benchmark1

method Add(x: int, y: int) returns (r: int)
 ensures r == x+y
{
  r := 0;
  assume r ==> x+y;
  return r;
}


// SPEC

method TestAdd(x: int, y: int) {
}
