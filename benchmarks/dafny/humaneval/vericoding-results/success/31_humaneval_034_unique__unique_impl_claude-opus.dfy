// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
predicate SeqContains(s: seq<int>, x: int)
{
  exists i :: 0 <= i < |s| && s[i] == x
}

function SeqToSet(s: seq<int>): set<int>
{
  set i | 0 <= i < |s| :: s[i]
}

function SortedInsert(s: seq<int>, x: int): seq<int>
  requires forall i, j :: 0 <= i < j < |s| ==> s[i] < s[j]
  ensures forall i, j :: 0 <= i < j < |SortedInsert(s, x)| ==> SortedInsert(s, x)[i] < SortedInsert(s, x)[j]
  ensures x in SortedInsert(s, x)
  ensures forall y :: y in s ==> y in SortedInsert(s, x)
  ensures forall y :: y in SortedInsert(s, x) ==> y in s || y == x
{
  if |s| == 0 then [x]
  else if x < s[0] then [x] + s
  else if x == s[0] then s
  else if |s| == 1 then s + [x]
  else if x < s[1] then [s[0], x] + s[1..]
  else [s[0]] + SortedInsert(s[1..], x)
}
// </vc-helpers>

// <vc-spec>
method unique(s: seq<int>) returns (result: seq<int>)

    ensures forall i, j :: 0 <= i < j < |result| ==> result[i] < result[j]
    ensures forall x :: x in result ==> x in s
    ensures forall x :: x in s ==> x in result
// </vc-spec>
// <vc-code>
{
  var sorted := [];
  var i := 0;
  
  while i < |s|
    invariant 0 <= i <= |s|
    invariant forall j, k :: 0 <= j < k < |sorted| ==> sorted[j] < sorted[k]
    invariant forall x :: x in sorted ==> x in s[..i]
    invariant forall x :: x in s[..i] ==> x in sorted
  {
    if !(s[i] in sorted) {
      sorted := SortedInsert(sorted, s[i]);
    }
    i := i + 1;
  }
  
  result := sorted;
}
// </vc-code>
