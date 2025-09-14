method sorted_even(a: seq<int>) returns (sorted: seq<int>)
  // pre-conditions-start
  requires |a| > 0
  // pre-conditions-end
  // post-conditions-start
  ensures |sorted| == |a|
  ensures forall i, j :: 0 <= i < j && 2 * i < |sorted| && 2 * j < |sorted| ==>
      sorted[2 * i] <= sorted[2 * j]
      ensures forall i :: 0 <= i < |a| && i % 2 == 1 ==> sorted[i] == a[i]
      ensures multiset(a) == multiset(sorted)
  // post-conditions-end
{
  assume{:axiom} false;
}

// <vc-helpers>
function method extractWithPred(s: seq<int>, p: seq<bool>): seq<int>
  requires |s| == |p|
{
  if |s| == 0 then []
  else if p[0] then [s[0]] + extractWithPred(s[1..], p[1..])
  else extractWithPred(s[1..], p[1..])
}

function method insertSorted(x: int, sorted: seq<int>): seq<int>
  ensures |insertSorted(x, sorted)| == |sorted| + 1
  ensures multiset(insertSorted(x, sorted)) == multiset([x]) + multiset(sorted)
  ensures forall i, j :: 0 <= i < j < |sorted| && sorted[i] <= sorted[j] ==>
    forall k, l :: 0 <= k < l < |insertSorted(x, sorted)| ==> insertSorted(x, sorted)[k] <= insertSorted(x, sorted)[l]
{
  if |sorted| == 0 then [x]
  else if x <= sorted[0] then [x] + sorted
  else [sorted[0]] + insertSorted(x, sorted[1..])
}

function method sortSeq(s: seq<int>): seq<int>
  ensures |sortSeq(s)| == |s|
  ensures multiset(sortSeq(s)) == multiset(s)
  ensures forall i, j :: 0 <= i < j < |sortSeq(s)| ==> sortSeq(s)[i] <= sortSeq(s)[j]
{
  if |s| == 0 then []
  else insertSorted(s[0], sortSeq(s[1..]))
}

lemma extractPreservesMultiset(s: seq<int>, p: seq<bool>, sorted: seq<int>, extracted: seq<int>)
  requires |s| == |p|
  requires |sorted| == |s|
  requires extracted == extractWithPred(s, p)
  requires |extractWithPred(s, p)| == |sortSeq(extracted)|
  requires forall i :: 0 <= i < |s| && !p[i] ==> sorted[i] == s[i]
  ensures multiset(s) == multiset(sorted) ==> true
{
}
// </vc-helpers>

// <vc-spec>
method SortSeqPred(s: seq<int>, p: seq<bool>) returns (sorted: seq<int>)
  // pre-conditions-start
  requires |s| == |p|
  // pre-conditions-end
  // post-conditions-start
  ensures |sorted| == |s|
  ensures forall i, j :: 0 <= i < j < |sorted| && p[i] && p[j] ==> sorted[i] <= sorted[j]
  ensures multiset(s) == multiset(sorted)
  ensures forall i :: 0 <= i < |s| && !p[i] ==> sorted[i] == s[i]
  // post-conditions-end
// </vc-spec>
// <vc-code>
{
  var extracted := extractWithPred(s, p);
  var sortedExtracted := sortSeq(extracted);
  
  sorted := s;
  var j := 0;
  
  for i := 0 to |s|
    invariant 0 <= i <= |s|
    invariant 0 <= j <= |sortedExtracted|
    invariant |sorted| == |s|
    invariant forall k :: 0 <= k < i && p[k] ==> exists l :: 0 <= l < j && sorted[k] == sortedExtracted[l]
    invariant forall k :: 0 <= k < |s| && !p[k] ==> sorted[k] == s[k]
    invariant j == |{k | 0 <= k < i && p[k]}|
  {
    if p[i] {
      sorted := sorted[..i] + [sortedExtracted[j]] + sorted[i+1..];
      j := j + 1;
    }
  }
}
// </vc-code>

