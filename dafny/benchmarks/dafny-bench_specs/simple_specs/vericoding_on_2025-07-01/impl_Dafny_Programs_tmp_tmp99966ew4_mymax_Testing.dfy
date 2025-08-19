//ATOM

method Max(a: int, b:int) returns (c: int)
  ensures c >= a && c>= b
{
  c := 0;
  assume c >= a && c>= b;
  return c;
}


// SPEC

method Testing()
{
}