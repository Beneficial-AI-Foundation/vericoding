// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed decreases clause and reconstruction logic */
function ExtractTrueIndices(s: seq<int>, p: seq<bool>): seq<int>
  requires |s| == |p|
  decreases |s|
{
  if |s| == 0 then []
  else if p[0] then [s[0]] + ExtractTrueIndices(s[1..], p[1..])
  else ExtractTrueIndices(s[1..], p[1..])
}

function FilterSmaller(xs: seq<int>, pivot: int): seq<int>
  decreases |xs|
{
  if |xs| == 0 then []
  else if xs[0] < pivot then [xs[0]] + FilterSmaller(xs[1..], pivot)
  else FilterSmaller(xs[1..], pivot)
}

function FilterLarger(xs: seq<int>, pivot: int): seq<int>
  decreases |xs|
{
  if |xs| == 0 then []
  else if xs[0] > pivot then [xs[0]] + FilterLarger(xs[1..], pivot)
  else FilterLarger(xs[1..], pivot)
}

function SortedSeq(xs: seq<int>): seq<int>
  decreases |xs|
{
  if |xs| <= 1 then xs
  else
    var pivot := xs[0];
    var rest := xs[1..];
    var smaller := FilterSmaller(rest, pivot);
    var larger := FilterLarger(rest, pivot);
    SortedSeq(smaller) + [pivot] + SortedSeq(larger)
}

function ReconstructSeq(s: seq<int>, p: seq<bool>, sortedTrue: seq<int>, nextTrueIndex: int): seq<int>
  requires |s| == |p|
  requires nextTrueIndex >= 0
  decreases |s|
{
  if |s| == 0 then []
  else if p[0] then
    if nextTrueIndex < |sortedTrue| then [sortedTrue[nextTrueIndex]] + ReconstructSeq(s[1..], p[1..], sortedTrue, nextTrueIndex + 1)
    else [s[0]] + ReconstructSeq(s[1..], p[1..], sortedTrue, nextTrueIndex)
  else [s[0]] + ReconstructSeq(s[1..], p[1..], sortedTrue, nextTrueIndex)
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
  /* code modified by LLM (iteration 5): fixed reconstruction with proper indexing */
  var trueElements := ExtractTrueIndices(s, p);
  var sortedTrueElements := SortedSeq(trueElements);
  sorted := ReconstructSeq(s, p, sortedTrueElements, 0);
}
// </vc-code>
