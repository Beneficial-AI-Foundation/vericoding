function binomial(n: int, k: int): int
    requires 0 <= k <= n
{
    if k == 0 || k == n then 1
    else if k == 1 then n
    else binomial(n-1, k-1) + binomial(n-1, k)
}

// <vc-helpers>
lemma BinomialPositive(n: int, k: int)
  requires 0 <= k <= n
  ensures binomial(n, k) > 0
  decreases n
{
  if k == 0 || k == n {
    assert binomial(n, k) == 1;
    assert 1 > 0;
  } else if k == 1 {
    assert binomial(n, k) == n;
    assert n > 0;
  } else {
    // by definition of binomial in this case
    assert binomial(n, k) == binomial(n - 1, k - 1) + binomial(n - 1, k);
    BinomialPositive(n - 1, k - 1);
    BinomialPositive(n - 1, k);
    assert binomial(n - 1, k - 1) > 0;
    assert binomial(n - 1, k) > 0;
    assert binomial(n, k) > 0;
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
  var r: seq<int> := [];
  var i := 0;
  while i <= k
    invariant 0 <= i <= k + 1
    invariant |r| == i
    invariant forall j :: 0 <= j < |r| ==> r[j] == binomial(k, j)
    invariant forall j :: 0 <= j < |r| ==> r[j] > 0
  {
    BinomialPositive(k, i);
    r := r + [binomial(k, i)];
    i := i + 1;
  }
  result := r;
}
// </vc-code>

