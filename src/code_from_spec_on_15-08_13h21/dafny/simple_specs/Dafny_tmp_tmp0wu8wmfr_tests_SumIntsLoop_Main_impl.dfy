//ATOM
function sumInts( n: int ): int
  requires n >= 0
{
  if n == 0 then
    0
  else
    sumInts(n-1)+n
}

/* code modified by LLM (iteration 1): added lemma to prove mathematical relationship */
lemma SumIntsFormula(n: int)
  requires n >= 0
  ensures sumInts(n) == n*(n+1)/2
{
  if n == 0 {
    // Base case: sumInts(0) == 0 == 0*(0+1)/2
  } else {
    // Inductive case
    SumIntsFormula(n-1);
    // sumInts(n) == sumInts(n-1) + n
    // By induction hypothesis: sumInts(n-1) == (n-1)*n/2
    // So sumInts(n) == (n-1)*n/2 + n == (n-1)*n/2 + 2*n/2 == ((n-1)*n + 2*n)/2 == (n*n - n + 2*n)/2 == (n*n + n)/2 == n*(n+1)/2
  }
}

//ATOM
method SumIntsLoop( n: int ) returns ( s: int )
  requires n >= 0
  ensures s == sumInts(n)
  ensures s == n*(n+1)/2
{
  s := 0;
  var i := 0;
  
  while i < n
    invariant 0 <= i <= n
    invariant s == sumInts(i)
  {
    i := i + 1;
    s := s + i;
  }
}

//IMPL Main
method Main()
{
  /* code modified by LLM (iteration 1): fixed method implementation to properly call SumIntsLoop and handle return value */
  var result := SumIntsLoop(100);
  print result;
}