function binomial(n: int, k: int): int
    requires 0 <= k <= n
{
    if k == 0 || k == n then 1
    else if k == 1 then n
    else binomial(n-1, k-1) + binomial(n-1, k)
}

// <vc-helpers>
lemma LemmaBinomialPositive(n: int, k: int)
  requires 0 <= k <= n
  ensures binomial(n, k) > 0
  decreases n
{
  if k == 0 || k == n {
    assert 1 > 0;
  } else if k == 1 {
    assert n >= 1;
  } else {
    assert 0 <= k - 1 <= n - 1;
    assert 0 <= k <= n - 1;
    LemmaBinomialPositive(n - 1, k - 1);
    LemmaBinomialPositive(n - 1, k);
    assert binomial(n - 1, k - 1) > 0 && binomial(n - 1, k) > 0;
  }
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
  var i := 0;
  result := [];
  while i <= k
    invariant 0 <= i <= k + 1
    invariant |result| == i
    invariant forall j :: 0 <= j < |result| ==> result[j] == binomial(k, j)
    invariant forall j :: 0 <= j < |result| ==> result[j] > 0
    decreases k - i + 1
  {
    LemmaBinomialPositive(k, i);
    result := result + [binomial(k, i)];
    i := i + 1;
  }
}
// </vc-code>

