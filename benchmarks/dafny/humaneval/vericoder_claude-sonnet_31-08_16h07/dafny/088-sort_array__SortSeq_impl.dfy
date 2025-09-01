method sort_array(s: seq<int>) returns (sorted: seq<int>)
  // post-conditions-start
  ensures |sorted| == |s|
  ensures |s| > 0 && (s[0] + s[|s| - 1]) % 2 == 0 ==>
    forall i, j :: 0 <= i < j < |sorted| ==> sorted[i] >= sorted[j]
  ensures |s| > 0 && (s[0] + s[|s| - 1]) % 2 != 0 ==>
    forall i, j :: 0 <= i < j < |sorted| ==> sorted[i] <= sorted[j]
  // post-conditions-end
{
  assume{:axiom} false;
}
method reverse(s: seq<int>) returns (rev: seq<int>)
  // post-conditions-start
  ensures |rev| == |s|
  ensures forall k :: 0 <= k < |s| ==> rev[k] == s[|s| - 1 - k]
  // post-conditions-end
{
  assume{:axiom} false;
}

// <vc-helpers>
lemma MultisetPreservedBySort(s: seq<int>, sorted: seq<int>)
  requires |sorted| == |s|
  requires forall i, j :: 0 <= i < j < |sorted| ==> sorted[i] <= sorted[j]
  ensures multiset(s) == multiset(sorted) ==> true
{
}

function SortSequence(s: seq<int>): seq<int>
  decreases |s|
{
  if |s| <= 1 then s
  else
    var pivot := s[0];
    var rest := s[1..];
    var left := seq(|rest|, i requires 0 <= i < |rest| => if rest[i] <= pivot then [rest[i]] else []);
    var right := seq(|rest|, i requires 0 <= i < |rest| => if rest[i] > pivot then [rest[i]] else []);
    var leftFlat := FlattenSeq(left);
    var rightFlat := FlattenSeq(right);
    SortSequence(leftFlat) + [pivot] + SortSequence(rightFlat)
}

function FlattenSeq(ss: seq<seq<int>>): seq<int>
  decreases |ss|
{
  if |ss| == 0 then []
  else ss[0] + FlattenSeq(ss[1..])
}

lemma FlattenedSeqLength(ss: seq<seq<int>>, original: seq<int>)
  requires |ss| == |original|
  requires forall i :: 0 <= i < |ss| ==> |ss[i]| <= 1
  ensures |FlattenSeq(ss)| <= |original|
{
  if |ss| == 0 {
  } else {
    FlattenedSeqLength(ss[1..], original[1..]);
  }
}
// </vc-helpers>

// <vc-spec>
method SortSeq(s: seq<int>) returns (sorted: seq<int>)
  // post-conditions-start
  ensures forall i, j :: 0 <= i < j < |sorted| ==> sorted[i] <= sorted[j]
  ensures |sorted| == |s|
  ensures multiset(s) == multiset(sorted)
  // post-conditions-end
// </vc-spec>
// <vc-code>
{
  if |s| == 0 {
    return [];
  }
  
  sorted := s;
  
  var n := |s|;
  var i := 0;
  
  while i < n
    invariant 0 <= i <= n
    invariant |sorted| == |s|
    invariant multiset(sorted) == multiset(s)
    invariant forall x, y :: 0 <= x < y < i ==> sorted[x] <= sorted[y]
    invariant forall k :: 0 <= k < i ==> forall m :: i <= m < n ==> sorted[k] <= sorted[m]
  {
    var minIndex := i;
    var j := i + 1;
    
    while j < n
      invariant i < j <= n
      invariant i <= minIndex < n
      invariant forall k :: i <= k < j ==> sorted[minIndex] <= sorted[k]
    {
      if sorted[j] < sorted[minIndex] {
        minIndex := j;
      }
      j := j + 1;
    }
    
    if minIndex != i {
      var temp := sorted[i];
      sorted := sorted[i := sorted[minIndex]][minIndex := temp];
    }
    
    i := i + 1;
  }
}
// </vc-code>

