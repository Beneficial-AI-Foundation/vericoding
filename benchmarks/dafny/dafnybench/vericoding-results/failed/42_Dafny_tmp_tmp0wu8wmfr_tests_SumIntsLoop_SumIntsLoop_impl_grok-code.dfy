function sumInts( n: int ): int
    requires n >= 0;
{
    if n == 0 then
        0
    else
        sumInts(n-1)+n
}

// <vc-helpers>
function sumInts( n: int ): int
    requires n >= 0
{
    if n == 0 then
        0
    else
        sumInts(n-1)+n
}

lemma SumIntsClosedForm(n: int)
  requires n >= 0
  ensures sumInts(n) == n * (n + 1) / 2
{
  if n == 0 {
    // Base case follows from definition
  } else {
    // Induction hypothesis
    SumIntsClosedForm(n - 1);
    calc {
      sumInts(n);
== 
      sumInts(n - 1) + n;
== 
      (n - 1) * n / 2 + n;
== { assert (n-1) * n / 2 + n == ((n-1)*n + 2*n)/2; 
     assert ((n-1)*n + 2*n)/2 == n*(n-1 + 2)/2;
     assert n*(n-1 + 2)/2 == n*(n+1)/2; }
      n * (n + 1) / 2;
    }
  }
}
// </vc-helpers>

// <vc-spec>
method SumIntsLoop( n: int ) returns ( s: int )
    requires n >= 0;
    ensures s == sumInts(n)
    ensures s == n*(n+1)/2;
// </vc-spec>
// <vc-code>
{
  var k := 0;
  var sum := 0;
  while k < n
    invariant 0 <= k <= n
    invariant sum == sumInts(k)
  {
    k := k + 1;
    sum := sum + k;
  }
  SumIntsClosedForm(n);
  s := sum;
}
// </vc-code>

