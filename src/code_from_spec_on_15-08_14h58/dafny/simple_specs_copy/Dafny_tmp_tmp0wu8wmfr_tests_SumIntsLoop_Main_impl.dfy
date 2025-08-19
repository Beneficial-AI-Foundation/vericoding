function sumInts( n: int ): int
  requires n >= 0
{
  if n == 0 then
    0
  else
    sumInts(n-1)+n
}


//ATOM
method SumIntsLoop( n: int ) returns ( s: int )
  requires n >= 0
  ensures s == sumInts(n)
  ensures s == n*(n+1)/2
{
  /* code modified by LLM (iteration 1): replaced assume statements with actual loop implementation */
  s := 0;
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant s == sumInts(i)
    /* code modified by LLM (iteration 2): added invariant to establish connection to arithmetic formula */
    invariant s == i*(i+1)/2
  {
    i := i + 1;
    s := s + i;
  }
  return s;
}


//IMPL 
method Main()
{
  var x := SumIntsLoop(100);
  print x;
}