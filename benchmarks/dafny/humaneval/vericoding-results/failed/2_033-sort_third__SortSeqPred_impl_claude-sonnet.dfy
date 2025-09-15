// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed list comprehension syntax in SortSeq */
function ExtractSortableElements(s: seq<int>, p: seq<bool>): seq<int>
  requires |s| == |p|
{
  if |s| == 0 then []
  else if p[0] then [s[0]] + ExtractSortableElements(s[1..], p[1..])
  else ExtractSortableElements(s[1..], p[1..])
}

function SortSeq(s: seq<int>): seq<int>
{
  if |s| <= 1 then s
  else
    var pivot := s[0];
    var rest := s[1..];
    var smaller := seq(|rest|, i requires 0 <= i < |rest| => rest[i]) |> seq(|rest|, i requires 0 <= i < |rest| && rest[i] <= pivot => rest[i]);
    var larger := seq(|rest|, i requires 0 <= i < |rest| && rest[i] > pivot => rest[i]);
    SortSeq(smaller) + [pivot] + SortSeq(larger)
}

function InsertSorted(value: int, sorted: seq<int>): seq<int>
{
  if |sorted| == 0 then [value]
  else if value <= sorted[0] then [value] + sorted
  else [sorted[0]] + InsertSorted(value, sorted[1..])
}
// </vc-helpers>

// <vc-spec>
method SortSeqPred(s: seq<int>, p: seq<bool>) returns (sorted: seq<int>)

  requires |s| == |p|

  ensures |sorted| == |s|
  ensures forall i, j :: 0 <= i < j < |sorted| && p[i] && p[j] ==> sorted[i] <= sorted[j]
  ensures multiset(s) == multiset(sorted)
  ensures forall i :: 0 <= i < |s| && !p[i] ==> sorted[i] == s[i]
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 5): simplified iterative bubble sort approach */
  sorted := s;
  var changed := true;
  while changed
    invariant |sorted| == |s|
    invariant multiset(s) == multiset(sorted)
    invariant forall k :: 0 <= k < |s| && !p[k] ==> sorted[k] == s[k]
  {
    changed := false;
    var i := 0;
    while i < |sorted| - 1
      invariant 0 <= i <= |sorted| - 1
      invariant |sorted| == |s|
      invariant multiset(s) == multiset(sorted)
      invariant forall k :: 0 <= k < |s| && !p[k] ==> sorted[k] == s[k]
    {
      if p[i] && p[i + 1] && sorted[i] > sorted[i + 1] {
        var temp := sorted[i];
        sorted := sorted[i := sorted[i + 1]][i + 1 := temp];
        changed := true;
      }
      i := i + 1;
    }
  }
}
// </vc-code>
