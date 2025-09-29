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
method sort_strings(list: seq<string>) returns (sorted: seq<string>)
    ensures |sorted| == |list|
    ensures multiset(sorted) == multiset(list)
// </vc-spec>
// <vc-code>
{
  sorted := list;
  var i := 0;
  while i < |sorted|
    invariant 0 <= i <= |sorted|
    invariant |sorted| == |list|
    invariant multiset(sorted) == multiset(list)
  {
    var j := i + 1;
    while j < |sorted|
      invariant i < j <= |sorted|
      invariant |sorted| == |list|
      invariant multiset(sorted) == multiset(list)
    {
      if !comparison(sorted[i], sorted[j], 0) {
        var temp := sorted[i];
        sorted := sorted[i := sorted[j]];
        sorted := sorted[j := temp];
      }
      j := j + 1;
    }
    i := i + 1;
  }
}
// </vc-code>
