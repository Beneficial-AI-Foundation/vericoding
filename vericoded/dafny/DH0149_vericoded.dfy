// <vc-preamble>
function comparison(a : string, b : string, i : int): bool
    requires 0 <= i <= |a| && 0 <= i <= |b|
    decreases |a| - i
    decreases |b| - i
    ensures (a == b) ==> comparison(a, b, i)
{
    if (i < |a| && i < |b|) then
        if a[i] < b[i] then
            true
        else if a[i] > b[i] then
            false
        else
            comparison(a, b, i + 1)
    else
        if |a| <= |b| then
            true
        else
            false
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method sort_lengths(list: seq<string>) returns (sorted: seq<string>)
    requires forall i : int :: 0 <= i < |list| ==> |list[i]| % 2 == 0
    ensures forall i : int :: 0 <= i < |sorted| ==> |sorted[i]| % 2 == 0
    ensures |sorted| == |list|
    ensures multiset(sorted) == multiset(list)
    ensures forall x : int, y : int :: 0 <= x < y < |sorted| ==> |sorted[x]| <= |sorted[y]|
// </vc-spec>
// <vc-code>
{
  sorted := list;
  var i := 0;
  while i < |sorted|
    invariant 0 <= i <= |sorted|
    invariant |sorted| == |list|
    invariant multiset(sorted) == multiset(list)
    invariant forall k : int :: 0 <= k < |sorted| ==> |sorted[k]| % 2 == 0
    invariant forall x : int, y : int :: 0 <= x < y < i ==> |sorted[x]| <= |sorted[y]|
    invariant forall x : int, y : int :: 0 <= x < i <= y < |sorted| ==> |sorted[x]| <= |sorted[y]|
  {
    var j := i;
    var minIdx := i;
    while j < |sorted|
      invariant i <= j <= |sorted|
      invariant i <= minIdx < |sorted|
      invariant forall k : int :: i <= k < j ==> |sorted[minIdx]| <= |sorted[k]|
    {
      if |sorted[j]| < |sorted[minIdx]| {
        minIdx := j;
      }
      j := j + 1;
    }
    if minIdx != i {
      var temp := sorted[i];
      sorted := sorted[i := sorted[minIdx]];
      sorted := sorted[minIdx := temp];
    }
    i := i + 1;
  }
}
// </vc-code>
