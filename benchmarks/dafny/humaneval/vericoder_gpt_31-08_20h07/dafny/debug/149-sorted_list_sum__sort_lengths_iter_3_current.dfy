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
predicate SortedByLen(s: seq<string>)
{
  forall x:int, y:int :: 0 <= x < y < |s| ==> |s[x]| <= |s[y]|
}

predicate EvenAll(s: seq<string>)
{
  forall i:int :: 0 <= i < |s| ==> |s[i]| % 2 == 0
}

lemma SortedInsert(acc: seq<string>, x: string, i:int)
  requires SortedByLen(acc)
  requires 0 <= i <= |acc|
  requires forall k:int :: 0 <= k < i ==> |acc[k]| < |x|
  requires i == |acc| || |x| <= |acc[i]|
  ensures SortedByLen(acc[..i] + [x] + acc[i..])
{
  var res := acc[..i] + [x] + acc[i..];
  assert forall p:int, q:int
           :: 0 <= p < q < |res|
           ==> |res[p]| <= |res[q]|
    by {
      if q < i {
        // both from left part acc[..i]
        assert res[p] == acc[p];
        assert res[q] == acc[q];
        assert |acc[p]| <= |acc[q]|;
      } else if p < i && q == i {
        // left part and x
        assert res[p] == acc[p];
        assert res[q
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
predicate SortedByLen(s: seq<string>)
{
  forall x:int, y:int :: 0 <= x < y < |s| ==> |s[x]| <= |s[y]|
}

predicate EvenAll(s: seq<string>)
{
  forall i:int :: 0 <= i < |s| ==> |s[i]| % 2 == 0
}

lemma SortedInsert(acc: seq<string>, x: string, i:int)
  requires SortedByLen(acc)
  requires 0 <= i <= |acc|
  requires forall k:int :: 0 <= k < i ==> |acc[k]| < |x|
  requires i == |acc| || |x| <= |acc[i]|
  ensures SortedByLen(acc[..i] + [x] + acc[i..])
{
  var res := acc[..i] + [x] + acc[i..];
  assert forall p:int, q:int
           :: 0 <= p < q < |res|
           ==> |res[p]| <= |res[q]|
    by {
      if q < i {
        // both from left part acc[..i]
        assert res[p] == acc[p];
        assert res[q] == acc[q];
        assert |acc[p]| <= |acc[q]|;
      } else if p < i && q == i {
        // left part and x
        assert res[p] == acc[p];
        assert res[q
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