// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
predicate IsSorted(s: seq<int>)
{
  forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
}

function Insert(x: int, s: seq<int>): seq<int>
  requires IsSorted(s)
  ensures IsSorted(Insert(x, s))
  ensures |Insert(x, s)| == |s| + 1
  ensures multiset(Insert(x, s)) == multiset(s) + multiset{x}
{
  if |s| == 0 then [x]
  else if x <= s[0] then [x] + s
  else [s[0]] + Insert(x, s[1..])
}
// </vc-helpers>

// <vc-spec>
method SortSeq(s: seq<int>) returns (sorted: seq<int>)

  ensures forall i, j :: 0 <= i < j < |sorted| ==> sorted[i] <= sorted[j]
  ensures |sorted| == |s|
  ensures multiset(s) == multiset(sorted)
// </vc-spec>
// <vc-code>
{
  sorted := [];
  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant IsSorted(sorted)
    invariant |sorted| == i
    invariant multiset(sorted) == multiset(s[..i])
  {
    sorted := Insert(s[i], sorted);
    i := i + 1;
  }
}
// </vc-code>
