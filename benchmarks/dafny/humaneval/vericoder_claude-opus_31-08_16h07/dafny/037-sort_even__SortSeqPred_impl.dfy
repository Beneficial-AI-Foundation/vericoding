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
  else 
    assert forall i, j :: 0 <= i < j < |sorted[1..]| ==> sorted[1..][i] <= sorted[1..][j];
    var rest := insertSorted(x, sorted[1..]);
    assert |rest| == |sorted[1..]| + 1;
    assert multiset(rest) == multiset([x]) + multiset(sorted[1..]);
    assert sorted[0] <= sorted[1] by { if |sorted| > 1 { assert sorted[0] <= sorted[1]; } }
    assert forall i :: 0 <= i < |rest| ==> sorted[0] <= rest[i] by {
      if x <= sorted[0] { assert false; }
      assert x > sorted[0];
      assert forall i :: 1 <= i < |sorted| ==> sorted[0] <= sorted[i];
    }
    assert multiset([sorted[0]] + rest) == multiset([sorted[0]]) + multiset(rest);
    assert multiset([sorted[0]]) + multiset(rest) == multiset([sorted[0]]) + multiset([x]) + multiset(sorted[1..]);
    assert |sorted| >= 1;
    assert sorted == [sorted[0]] + sorted[1..];
    assert multiset(sorted) == multiset([sorted[0]]) + multiset(sorted[1..]);
    [sorted[0]] + rest
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
    assert multiset(tail) == multiset(s[1..]);
    var result := insertSorted(s[0], tail);
    assert multiset(result) == multiset([s[0]]) + multiset(tail);
    assert multiset(result) == multiset([s[0]]) + multiset(s[1..]);
    assert s == [s[0]] + s[1..];
    assert multiset(s) == multiset([s[0]]) + multiset(s[1..]);
    result
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
  if i == j {
    assert p[i..j] == [];
    assert countTrue([], 0) == 0;
  } else {
    countTrueProperty(p, i, j-1);
    assert p[i..j] == p[i..j-1] + [p[j-1]];
    assert p[i..j][j-i-1] == p[j-1];
    
    if p[j-1] {
      calc {
        countTrue(p[i..j], j-i);
      == { assert p[i..j] == p[i..j-1] + [p[j-1]]; }
        1 + countTrue(p[i..j], j-i-1);
      == { }
        1 + countTrue(p[i..j-1], j-i-1);
      == { countTrueProperty(p, i, j-1); }
        1 + (countTrue(p, j-1) - countTrue(p, i));
      == { assert countTrue(p, j) == 1 + countTrue(p, j-1); }
        countTrue(p, j) - countTrue(p, i);
      }
    } else {
      calc {
        countTrue(p[i..j], j-i);
      == { }
        countTrue(p[i..j], j-i-1);
      == { }
        countTrue(p[i..j-1], j-i-1);
      == { countTrueProperty(p, i, j-1); }
        countTrue(p, j-1) - countTrue(p, i);
      == { assert countTrue(p, j) == countTrue(p, j-1); }
        countTrue(p, j) - countTrue(p, i);
      }
    }
  }
}

function extractPrefixWithPred(s: seq<int>, p: seq<bool>, n: int): seq<int>
  requires |s| == |p|
  requires 0 <= n <= |s|
{
  if n == 0 then []
  else if p[n-1] then extractPrefixWithPred(s, p, n-1) + [s[n-1]]
  else extractPrefixWithPred(s, p, n-1)
}

lemma extractPrefixMultiset(s: seq<int>, p: seq<bool>, n: int)
  requires |s| == |p|
  requires 0 <= n <= |s|
  ensures |extractPrefixWithPred(s, p, n)| == countTrue(p, n)
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
    invariant extracted == extractPrefixWithPred(s, p, i)
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
    invariant multiset(sorted[..i]) == multiset(s[..i])
  {
    if p[i] {
      countTrueProperty(p, i, i+1);
      assert j < |sortedExtracted| by {
        assert countTrue(p, i+1) == countTrue(p, i) + 1;
        assert j == countTrue(p, i);
        assert |sortedExtracted| == |extracted|;
        assert |extracted| == countTrue(p, |s|);
        assert i < |s|;
        assert countTrue(p, i) < countTrue(p, |s|);
      }
      sorted := sorted + [sortedExtracted[j]];
      j := j + 1;
    } else {
      sorted := sorted + [s[i]];
    }
  }
  
  assert |sorted| == |s|;
  assert multiset(sorted) == multiset(s);
}
// </vc-code>

