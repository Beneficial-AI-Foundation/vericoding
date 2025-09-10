predicate ValidInput(n: int, aa: seq<int>)
{
    n >= 2 &&
    |aa| == n - 1 &&
    forall i :: 0 <= i < |aa| ==> 1 <= aa[i] < i + 2
}

function SubordinateCount(aa: seq<int>, boss_id: int): int
{
    |set j | 0 <= j < |aa| && aa[j] == boss_id|
}

predicate ValidOutput(n: int, aa: seq<int>, result: seq<int>)
{
    |result| == n &&
    forall i :: 0 <= i < n ==> result[i] >= 0 &&
    forall i :: 0 <= i < n ==> result[i] == SubordinateCount(aa, i + 1)
}

// <vc-helpers>
lemma LemmaSubordinateCountBound(aa: seq<int>, boss_id: int)
  ensures 0 <= SubordinateCount(aa, boss_id)
{
}

lemma LemmaSubordinateCountZero(aa: seq<int>, boss_id: int)
  requires boss_id ∉ set j | 0 <= j < |aa| :: aa[j]
  ensures SubordinateCount(aa, boss_id) == 0
{
}

lemma LemmaSubordinateCountNonZero(aa: seq<int>, boss_id: int, index: int)
  requires 0 <= index < |aa| && aa[index] == boss_id
  ensures SubordinateCount(aa, boss_id) >= 1
{
}

lemma LemmaSubordinateCountAdd(aa: seq<int>, boss_id: int, i: int)
  requires 0 <= i < |aa|
  ensures SubordinateCount(aa, boss_id) == SubordinateCount(aa[..i], boss_id) + SubordinateCount(aa[i..], boss_id)
{
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, aa: seq<int>) returns (result: seq<int>)
    requires ValidInput(n, aa)
    ensures ValidOutput(n, aa, result)
// </vc-spec>
// <vc-code>
{
  result := new int[n];
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant forall k :: 0 <= k < i ==> result[k] == SubordinateCount(aa, k + 1)
    invariant forall k :: i <= k < n ==> result[k] == 0
  {
    result[i] := 0;
    i := i + 1;
  }
  
  var j := 0;
  while j < |aa|
    invariant 0 <= j <= |aa|
    invariant forall k :: 0 <= k < n ==> result[k] == |set l | 0 <= l < j && aa[l] == k + 1|
  {
    var boss := aa[j];
    if boss > 0 && boss <= n {
      result[boss - 1] := result[boss - 1] + 1;
    }
    j := j + 1;
  }
}
// </vc-code>

