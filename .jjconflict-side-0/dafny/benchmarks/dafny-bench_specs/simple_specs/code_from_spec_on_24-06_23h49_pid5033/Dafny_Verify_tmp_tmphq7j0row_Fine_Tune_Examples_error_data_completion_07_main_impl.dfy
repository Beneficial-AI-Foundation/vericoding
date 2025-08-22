//IMPL main
method main(n: int) returns (a: int, b: int)
  requires n >= 0
  ensures a + b == 3 * n
{
  a := 3 * n;
  b := 0;
}