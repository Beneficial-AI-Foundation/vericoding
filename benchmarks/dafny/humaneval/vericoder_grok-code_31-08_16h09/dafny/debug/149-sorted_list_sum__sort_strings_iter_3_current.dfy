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

// <vc-helpers>
method insert(sorted : seq<string>, x : string) returns (newsorted : seq<string>) 
  requires forall k : int :: 0 <= k < |sorted|-1 ==> comparison(sorted[k], sorted[k+1], 0)
  ensures |newsorted| == |sorted| + 1
  ensures multiset(newsorted) == multiset(sorted) + multiset([x])
  ensures forall k : int :: 0 <= k < |newsorted|-1 ==> comparison(newsorted[k], newsorted[k+1], 0)
{
  var pos := 0;
  while pos < |sorted| && !comparison(x, sorted[pos], 0)
    invariant 0 <= pos <= |sorted|
    invariant forall k : int :: 0 <= k < pos ==> forall p : int :: pos <= p < |sorted| ==> comparison(sorted[k], sorted[p], 0)
    decreases |sorted| - pos
  {
    pos := pos + 1;
  }
  newsorted := sorted[..pos] + [x] + sorted[pos..];
}
// </vc-helpers>

// <vc-spec>
method sort_strings(list: seq<string>) returns (sorted: seq<string>)
    ensures |sorted| == |list|
    ensures multiset(sorted) == multiset(list)
// </vc-spec>
// <vc-code>
sorted := [];
  var i := 0;
  while i < |list|
    invariant 0 <= i <= |list|
    invariant |sorted| == i
    invariant multiset(sorted) == multiset(list[..i])
    invariant forall k : int :: 0 <= k < |sorted|-1 ==> comparison(sorted[k], sorted[k+1], 0)
    decreases |list| - i
  {
    var temp := insert(sorted, list[i]);
    sorted := temp;
    i := i + 1;
  }
// </vc-code>

method sort_lengths(list: seq<string>) returns (sorted: seq<string>)
    requires forall i : int :: 0 <= i < |list| ==> |list[i]| % 2 == 0
    ensures forall i : int :: 0 <= i < |sorted| ==> |sorted[i]| % 2 == 0
    ensures |sorted| == |list|
    ensures multiset(sorted) == multiset(list)
    ensures forall x : int, y : int :: 0 <= x < y < |sorted| ==> |sorted[x]| <= |sorted[y]|
{
  assume{:axiom} false;
}
method sorted_list_sum(list: seq<string>) returns (sorted: seq<string>)
    requires |list| > 0
    ensures |sorted| <= |list|
    ensures forall i : int :: 0 <= i < |sorted| ==> |sorted[i]| % 2 == 0
    ensures forall x : int, y : int :: 0 <= x < y < |sorted| ==> |sorted[x]| <= |sorted[y]|
    ensures multiset(sorted) <= multiset(list)
{
  assume{:axiom} false;
}