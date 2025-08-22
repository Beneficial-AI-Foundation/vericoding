//ATOM

method Mul(x: int, y: int) returns (r: int)
 ensures r == x*y
{
  r := x * y;
}


//ATOM

method TestMul(x: int, y: int) {
}


//ATOM

method TestAdd(x: int, y: int) {
}


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
  r := x + y;
}


//IMPL

// ---------------------------

method Main() {
 /* code modified by LLM (iteration 1): Fixed method calls to properly handle return values and ensure proper execution flow */
 var result1 := Add(3, 180);
 TestAdd(3, 180);
 var result2 := Add(3, -180);
 TestAdd(3, -180);
 var result3 := Add(0, 1);
 TestAdd(0, 1);

 var result4 := Mul(3, 180);
 TestMul(3, 180);
 var result5 := Mul(3, -180);
 TestMul(3, -180);
 var result6 := Mul(180, 3);
 TestMul(180, 3);
 var result7 := Mul(-180, 3);
 TestMul(-180, 3);
 var result8 := Mul(0, 1);
 TestMul(0, 1);
 var result9 := Mul(1, 0);
 TestMul(1, 0);
}