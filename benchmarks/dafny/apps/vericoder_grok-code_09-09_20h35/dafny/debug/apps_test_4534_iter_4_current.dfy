function binomial(n: int, k: int): int
    requires 0 <= k <= n
{
    if k == 0 || k == n then 1
    else if k == 1 then n
    else binomial(n-1, k-1) + binomial(n-1, k)
}

// <vc-helpers>
function binomial(n: int, k: int): int
    requires 0 <= k <= n
    decreases n
    ensures result > 0
{
    if k == 0 || k == n then 1
    else if k == 1 then n
    else binomial(n-1, k-1) + binomial(n-1, k)
}
// </vc-helpers>

// <vc-spec>
method getRow(k: int) returns (result: seq<int>)
    requires 0 <= k <= 33
    ensures |result| == k + 1
    ensures forall i :: 0 <= i < |result| ==> result[i] == binomial(k, i)
    ensures forall i :: 0 <= i < |result| ==> result[i] > 0
// </vc-spec>
// <vc-code>
{
  result := [];
  var i := 0;
  while i <= k
    invariant 0 <= i <= k + 1
    invariant forall p :: 0 <= p < i ==> result[p] == binomial(k, p)
    invariant |result| == i
    decreases k - i
  {
    result := result + [binomial(k, i)];
    i := i + 1;
  }
}
// </vc-code>

