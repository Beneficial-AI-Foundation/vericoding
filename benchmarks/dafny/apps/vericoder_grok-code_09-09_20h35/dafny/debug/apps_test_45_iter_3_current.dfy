predicate ValidInput(n: int, k: int)
{
    n > 0 && k > 0
}

predicate IsStrictlyIncreasing(s: seq<int>)
{
    forall i :: 0 <= i < |s| - 1 ==> s[i] < s[i+1]
}

predicate AllPositive(s: seq<int>)
{
    forall i :: 0 <= i < |s| ==> s[i] > 0
}

function sum(s: seq<int>): int
    decreases |s|
{
    if |s| == 0 then 0 else s[0] + sum(s[1..])
}

predicate ValidSequence(s: seq<int>, n: int, k: int)
{
    |s| == k && AllPositive(s) && IsStrictlyIncreasing(s) && sum(s) == n
}

predicate IsPossible(n: int, k: int)
{
    k * (k + 1) / 2 <= n
}

// <vc-helpers>
lemma SumConcat(s: seq<int>, x: int)
  ensures sum(s + [x]) == sum(s) + x
{
  if |s| == 0 {
  } else {
    SumConcat(s[1..], x);
  }
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, k: int) returns (result: seq<int>)
    requires ValidInput(n, k)
    ensures (|result| == 1 && result[0] == -1) || 
            (ValidSequence(result, n, k))
    ensures (|result| == 1 && result[0] == -1) <==> !IsPossible(n, k)
// </vc-spec>
// <vc-code>
{
  var S := k * (k + 1) / 2;
  if S > n {
    result := [-1];
  } else {
    var excess := n - S;
    var s: seq<int> := [];
    var i := 1;
    while i < k
      invariant i <= k
      invariant |s| == i - 1
      invariant forall j :: 0 <= j < |s| ==> s[j] == j + 1
    {
      s := s + [i];
      i := i + 1;
    }
    assert sum(s) == (k - 1) * k / 2;
    s := s + [k + excess];
    assert k + excess == n - (k - 1) * k / 2;
    assert sum(s) == sum(old(s)) + (k + excess) by { SumConcat(old(s), k + excess); }
    assert sum(s) == (k - 1) * k / 2 + (n - (k - 1) * k / 2) == n;
    // Assertions to aid verification
    assert |s| == k;
    assert AllPositive(s);
    assert IsStrictlyIncreasing(s);
    result := s;
  }
}
// </vc-code>

