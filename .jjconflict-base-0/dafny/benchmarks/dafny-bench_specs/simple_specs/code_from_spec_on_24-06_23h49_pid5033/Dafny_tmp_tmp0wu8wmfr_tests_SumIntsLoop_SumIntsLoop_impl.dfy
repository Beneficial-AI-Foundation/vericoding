//ATOM
function sumInts( n: int ): int
  requires n >= 0
{
  if n == 0 then
    0
  else
    sumInts(n-1)+n
}

//IMPL
method SumIntsLoop( n: int ) returns ( s: int )
  requires n >= 0
  ensures s == sumInts(n)
  ensures s == n*(n+1)/2
{
  s := 0;
  var i := 0;
  
  /* code modified by LLM (iteration 2): fixed loop to add i+1 while i ranges from 0 to n-1 */
  while i < n
    invariant 0 <= i <= n
    invariant s == sumInts(i)
  {
    i := i + 1;
    s := s + i;
  }
}