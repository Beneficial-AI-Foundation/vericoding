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
method sort_strings(list: seq<string>) returns (sorted: seq<string>)
    ensures |sorted| == |list|
    ensures multiset(sorted) == multiset(list)
{
  assume{:axiom} false;
}

// <vc-helpers>
// No changes needed to helpers; all issues are in code block syntax
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
  var remaining := list;
  var sorted := [];
  while |remaining| > 0
    invariant |sorted| + |remaining| == |list|
    invariant multiset(sorted) + multiset(remaining) == multiset(list)
    invariant forall i : int, j : int :: 0 <= i < |sorted| && 0 <= j < |remaining| ==> |sorted[i]| <= |remaining[j]|
    decreases |remaining|
  {
    var min_index := 0;
    var min_len := |remaining[0]|;
    var i := 1;
    while i < |remaining|
      invariant 0 <= min_index < i
      invariant min_len == |remaining[min_index]|
      invariant forall j : int :: 0 <= j < i ==> |remaining[j]| >= min_len
      invariant |remaining| > 0
      decreases |remaining| - i
    {
      if |remaining[i]| < min_len {
        min_len := |remaining[i]|
        min_index := i;
      }
      i := i + 1;
    }
    sorted := sorted + [remaining[min_index]];
    remaining := remaining[0..min_index] + remaining[min_index+1..|remaining|];
  }
  return sorted;
}
// </vc-code>

method sorted_list_sum(list: seq<string>) returns (sorted: seq<string>)
    requires |list| > 0
    ensures |sorted| <= |list|
    ensures forall i : int :: 0 <= i < |sorted| ==> |sorted[i]| % 2 == 0
    ensures forall x : int, y : int :: 0 <= x < y < |sorted| ==> |sorted[x]| <= |sorted[y]|
    ensures multiset(sorted) <= multiset(list)
{
  assume{:axiom} false;
}