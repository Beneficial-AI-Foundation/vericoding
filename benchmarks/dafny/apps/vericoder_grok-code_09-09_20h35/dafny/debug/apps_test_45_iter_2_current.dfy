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
// Empty as no additional helpers needed for this fix
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
    s := s + [k + excess];
    // Assertions to aid verification
    assert |s| == k;
    assert AllPositive(s);
    assert IsStrictlyIncreasing(s);
    assert sum(s) == n;
    result := s;
  }
}
// </vc-code>

