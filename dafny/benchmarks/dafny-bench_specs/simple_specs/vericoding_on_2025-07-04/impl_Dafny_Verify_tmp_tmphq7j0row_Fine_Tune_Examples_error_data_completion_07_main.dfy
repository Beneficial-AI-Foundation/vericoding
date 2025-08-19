//IMPL 
method main(n: int) returns (a: int, b: int)
  requires n >= 0
  ensures a + b == 3 * n
{
  a := 0;
  b := 3 * n;
}