// RUN: %dafny /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// Spec# and Boogie and Chalice:  The program will be
// the same, except that these languages do not check
// for any kind of termination.  Also, in Spec#, there
// is an issue of potential overflows.

// Benchmark1

//IMPL Add
method Add(x: int, y: int) returns (r: int)
  ensures r == x+y;
{
  r := x + y;
}

//ATOM Mul
method Mul(x: int, y: int) returns (r: int)
  ensures r == x * y;
{
  r := x * y;
}

// ---------------------------

//ATOM Main
method Main()
{
  TestAdd();
  TestMul();
}

//ATOM TestAdd
method TestAdd()
{
  var result := Add(3, 5);
  assert result == 8;
}

//ATOM TestMul
method TestMul()
{
  var result := Mul(4, 6);
  assert result == 24;
}