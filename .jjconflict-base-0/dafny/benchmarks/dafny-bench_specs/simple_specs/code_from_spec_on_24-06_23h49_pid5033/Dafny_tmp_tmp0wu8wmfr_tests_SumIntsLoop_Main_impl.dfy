//ATOM
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
  s := 0;
  assume s == sumInts(n);
  assume s == n*(n+1)/2;
  return s;
}


//IMPL
method Main()
{
  var x := SumIntsLoop(100);
  print x;
}