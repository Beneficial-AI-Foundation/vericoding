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
function Insert(s: string, sorted_list: seq<string>): seq<string>
  requires forall i, j :: 0 <= i < j < |sorted_list| ==> |sorted_list[i]| <= |sorted_list[j]|
  ensures |Insert(s, sorted_list)| == |sorted_list| + 1
  ensures multiset(Insert(s, sorted_list)) == multiset({s}) + multiset(sorted_list)
  ensures forall i, j :: 0 <= i < j < |Insert(s, sorted_list)| ==> |Insert(s, sorted_list)[i]| <= |Insert(s, sorted_list)[j]|
  decreases |sorted_list|
{
  if |sorted_list| == 0 then [s]
  else if |s| <= |sorted_list[0]| then [s] + sorted_list
  else [sorted_list[0]] + Insert(s, sorted_list[1..])
}

function Sort(list: seq<string>): seq<string>
  ensures |Sort(list)| == |list|
  ensures multiset(Sort(list)) == multiset(list)
  ensures forall i, j :: 0 <= i < j < |Sort(list)| ==> |Sort(list)[i]| <= |Sort(list)[j]|
  decreases |list|
{
  if |list| == 0 then []
  else Insert(list[0], Sort(list[1..]))
}
// </vc-helpers>

// <vc-spec>
method sorted_list_sum(list: seq<string>) returns (sorted: seq<string>)
    requires |list| > 0
    ensures |sorted| <= |list|
    ensures forall i : int :: 0 <= i < |sorted| ==> |sorted[i]| % 2 == 0
    ensures forall x : int, y : int :: 0 <= x < y < |sorted| ==> |sorted[x]| <= |sorted[y]|
    ensures multiset(sorted) <= multiset(list)
// </vc-spec>
// <vc-code>
{
  var evens: seq<string> := [];
  var i := 0;
  while i < |list|
    invariant 0 <= i <= |list|
    invariant multiset(evens) <= multiset(list[..i])
    invariant forall s :: s in evens ==> |s| % 2 == 0
  {
    if |list[i]| % 2 == 0 {
      evens := evens + [list[i]];
    }
    i := i + 1;
  }
  sorted := Sort(evens);
}
// </vc-code>
