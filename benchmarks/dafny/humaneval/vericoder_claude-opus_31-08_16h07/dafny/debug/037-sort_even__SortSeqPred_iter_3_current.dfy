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
function extractWithPred(s: seq<int>, p: seq<bool>): seq<int>
  requires |s| == |p|
{
  if |s| == 0 then []
  else if p[0] then [s[0]] + extractWithPred(s[1..], p[1..])
  else extractWithPred(s[1..], p[1..])
}

function insertSorted(x: int, sorted: seq<int>): seq<int>
  requires forall i, j :: 0 <= i < j < |sorted| ==> sorted[i] <= sorted[j]
  ensures |insertSorted(x, sorted)| == |sorted| + 1
  ensures multiset(insertSorted(x, sorted)) == multiset([x]) + multiset(sorted)
  ensures forall i, j :: 0 <= i < j < |insertSorted(x, sorted)| ==> insertSorted(x, sorted)[i] <= insertSorted(x, sorted)[j]
{
  if |sorted| == 0 then [x]
  else if x <= sorted[0] then [x] + sorted
  else [sorted[0]] + insertSorted(x, sorted[1..])
}

function sortSeq(s: seq<int>): seq<int>
  ensures |sortSeq(s)| == |s|
  ensures multiset(sortSeq(s)) == multiset(s)
  ensures forall i, j :: 0 <= i < j < |sortSeq(s)| ==> sortSeq(s)[i] <= sortSeq(s)[j]
  decreases |s|
{
  if |s| == 0 then []
  else 
    var tail := sortSeq(s[1..]);
    insertSorted(s[0], tail)
}

function countTrue(p: seq<bool>, i: int): int
  requires 0 <= i <= |p|
  ensures countTrue(p, i) >= 0
  ensures countTrue(p, i) <= i
{
  if i == 0 then 0
  else if p[i-1] then 1 + countTrue(p, i-1)
  else countTrue(p, i-1)
}

lemma extractPreservesElements(s: seq<int>, p: seq<bool>)
  requires |s| == |p|
  ensures forall x :: x in extractWithPred(s, p) ==> exists i :: 0 <= i < |s| && p[i] && s[i] == x
{
}

lemma sortSeqPreservesMultiset(s: seq<int>)
  ensures multiset(sortSeq(s)) == multiset(s)
{
}

lemma countTrueProperty(p: seq<bool>, i: int, j: int)
  requires 0 <= i <= j <= |p|
  ensures countTrue(p, j) - countTrue(p, i) == countTrue(p[i..j], j-i)
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
  var extracted := [];
  var extractedIndices := [];
  for i := 0 to |s|
    invariant 0 <= i <= |s|
    invariant |extracted| == countTrue(p, i)
    invariant |extracted| == |extractedIndices|
    invariant forall j :: 0 <= j < |extracted| ==> 0 <= extractedIndices[j] < i && p[extractedIndices[j]] && s[extractedIndices[j]] == extracted[j]
    invariant forall j, k :: 0 <= j < k < |extracted| ==> extractedIndices[j] < extractedIndices[k]
  {
    if p[i] {
      extracted := extracted + [s[i]];
      extractedIndices := extractedIndices + [i];
    }
  }
  
  var sortedExtracted := sortSeq(extracted);
  assert multiset(sortedExtracted) == multiset(extracted);
  
  sorted := [];
  var j := 0;
  for i := 0 to |s|
    invariant 0 <= i <= |s|
    invariant 0 <= j <= |sortedExtracted|
    invariant |sorted| == i
    invariant j == countTrue(p, i)
    invariant forall k :: 0 <= k < i && !p[k] ==> sorted[k] == s[k]
    invariant j <= |sortedExtracted|
    invariant forall k :: 0 <= k < j ==> exists l :: 0 <= l < i && p[l] && sorted[l] == sortedExtracted[k]
    invariant forall k, l :: 0 <= k < l < i && p[k] && p[l] ==> 
      exists m, n :: 0 <= m < n < j && sorted[k] == sortedExtracted[m] && sorted[l] == sortedExtracted[n]
    invariant multiset(sorted[..i]) + multiset(sortedExtracted[j..]) + multiset(s[i..]) == multiset(s) + multiset(sortedExtracted)
  {
    if p[i] {
      assert j < |sortedExtracted|;
      sorted := sorted + [sortedExtracted[j]];
      j := j + 1;
    } else {
      sorted := sorted + [s[i]];
    }
  }
}
// </vc-code>

