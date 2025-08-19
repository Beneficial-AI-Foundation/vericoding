//ATOM
function sumNegativesTo( a:array<int>, n:int ) : int
 requires 0 <= n && n <= a.Length
 reads a
{
 if (n == 0) then 0 else if a[n-1] < 0 then sumNegativesTo(a, n-1) + a[n-1] else sumNegativesTo(a, n-1)
}

//IMPL 
method SumOfNegatives(a: array<int>) returns (result: int)
  /* code modified by LLM (iteration 1): removed unnecessary null check since array<int> is non-null by default */
  ensures result == sumNegativesTo(a, a.Length)
{
  result := 0;
  var i := 0;
  
  while i < a.Length
    invariant 0 <= i <= a.Length
    invariant result == sumNegativesTo(a, i)
  {
    if a[i] < 0 {
      result := result + a[i];
    }
    i := i + 1;
  }
}