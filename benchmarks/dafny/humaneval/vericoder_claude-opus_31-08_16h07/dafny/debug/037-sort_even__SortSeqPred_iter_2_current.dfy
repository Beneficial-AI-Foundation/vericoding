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
  ensures |insertSorted(x, sorted)| == |sorted| + 1
  ensures multiset(insertSorted(x, sorted)) == multiset([x]) + multiset(sorted)
  ensures forall i, j :: 0 <= i < j < |sorted| && sorted[i] <= sorted[j] ==>
    forall k, l :: 0 <= k < l < |insertSorted(x, sorted)| ==> insertSorted(x, sorted)[k] <= insertSorted(x, sorted)[l]
{
  if |sorted| == 0 then [x]
  else if x <= sorted[0] then [x] + sorted
  else [sorted[0]] + insertSorted(x, sorted[1..])
}

function sortSeq(s: seq<int>): seq<int>
  ensures |sortSeq(s)| == |s|
  ensures multiset(sortSeq(s)) == multiset(s)
  ensures forall i, j :: 0 <= i < j < |sortSeq(s)| ==> sortSeq(s)[i] <= sortSeq(s)[j]
{
  if |s| == 0 then []
  else insertSorted(s[0], sortSeq(s[1..]))
}

function countTrue(p: seq<bool>, i: int): int
  requires 0 <= i <= |p|
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
  for i := 0 to |s|
    invariant 0 <= i <= |s|
    invariant |extracted| == countTrue(p, i)
    invariant forall j :: 0 <= j < |extracted| ==> exists k :: 0 <= k < i && p[k] && s[k] == extracted[j]
  {
    if p[i] {
      extracted := extracted + [s[i]];
    }
  }
  
  var sortedExtracted := [];
  for i := 0 to |extracted|
    invariant 0 <= i <= |extracted|
    invariant |sortedExtracted| == i
    invariant forall j, k :: 0 <= j < k < i ==> sortedExtracted[j] <= sortedExtracted[k]
    invariant multiset(sortedExtracted) == multiset(extracted[..i])
  {
    var j := 0;
    while j < |sortedExtracted| && sortedExtracted[j] <= extracted[i]
      invariant 0 <= j <= |sortedExtracted|
      invariant forall k :: 0 <= k < j ==> sortedExtracted[k] <= extracted[i]
    {
      j := j + 1;
    }
    sortedExtracted := sortedExtracted[..j] + [extracted[i]] + sortedExtracted[j..];
  }
  
  sorted := [];
  var j := 0;
  for i := 0 to |s|
    invariant 0 <= i <= |s|
    invariant 0 <= j <= |sortedExtracted|
    invariant |sorted| == i
    invariant j == countTrue(p, i)
    invariant forall k :: 0 <= k < i && !p[k] ==> sorted[k] == s[k]
    invariant forall k :: 0 <= k < j ==> exists l :: 0 <= l < i && p[l] && sorted[l] == sortedExtracted[k]
    invariant forall k, l :: 0 <= k < l < i && p[k] && p[l] ==> 
      exists m, n :: 0 <= m < n < j && sorted[k] == sortedExtracted[m] && sorted[l] == sortedExtracted[n]
  {
    if p[i] {
      sorted := sorted + [sortedExtracted[j]];
      j := j + 1;
    } else {
      sorted := sorted + [s[i]];
    }
  }
}
// </vc-code>

