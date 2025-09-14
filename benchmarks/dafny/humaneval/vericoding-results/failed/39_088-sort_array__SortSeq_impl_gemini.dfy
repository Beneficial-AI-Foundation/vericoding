// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
predicate Sorted(s: seq<int>) {
  forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
}

/* helper modified by LLM (iteration 4): fixed function signature syntax from 'returns' to ':' */
function Insert(s: seq<int>, val: int): (result: seq<int>)
  requires Sorted(s)
  ensures Sorted(result)
  ensures multiset(result) == multiset(s) + multiset{val}
  ensures |result| == |s| + 1
{
  if |s| == 0 then [val]
  else if val < s[0] then [val] + s
  else [s[0]] + Insert(s[1..], val)
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
  /* code modified by LLM (iteration 4): Fixed a compilation error in a helper function. */
  sorted := [];
  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant Sorted(sorted)
    invariant |sorted| == i
    invariant multiset(s) == multiset(sorted) + multiset(s[i..])
  {
    sorted := Insert(sorted, s[i]);
    i := i + 1;
  }
}
// </vc-code>
