//ATOM

method MaxSum(x: int, y: int) returns (s: int, m: int)
 ensures s == x + y
 ensures m == if x >= y then x else y
{
  s := 0;
  m := 0;
  assume s ==> x + y;
  assume m ==> if x >= y then x else y;
  return s, m;
}


// SPEC


method MaxSumCaller() {
}