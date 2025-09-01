method uniqueSorted(s: seq<int>) returns (result: seq<int>)
    // pre-conditions-start
    requires forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
    // pre-conditions-end
    // post-conditions-start
    ensures forall i, j :: 0 <= i < j < |result| ==> result[i] < result[j]
    ensures forall x :: x in result ==> x in s
    ensures forall x :: x in s ==> x in result
    // post-conditions-end
{
  assume{:axiom} false;
}
method unique(s: seq<int>) returns (result: seq<int>)
    // post-conditions-start
    ensures forall i, j :: 0 <= i < j < |result| ==> result[i] < result[j]
    ensures forall x :: x in result ==> x in s
    ensures forall x :: x in s ==> x in result
    // post-conditions-end
{
  assume{:axiom} false;
}

// <vc-helpers>
lemma SortedUniqueLemma(s: seq<int>)
  requires forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
  ensures forall i, j :: 0 <= i < j < |s| && s[i] == s[j] ==> false
{
}

lemma UniqueSortedLemma(s: seq<int>, result: seq<int>)
  requires forall i, j :: 0 <= i < j < |result| ==> result[i] < result[j]
  requires forall x :: x in result ==> x in s
  requires forall x :: x in s ==> x in result
  ensures forall i, j :: 0 <= i < j < |result| ==> result[i] <= result[j]
{
}

function method RemoveDuplicates(sorted: seq<int>): seq<int>
  requires forall i, j :: 0 <= i < j < |sorted| ==> sorted[i] <= sorted[j]
  ensures forall i, j :: 0 <= i < j < |RemoveDuplicates(sorted)| ==> RemoveDuplicates(sorted)[i] < RemoveDuplicates(sorted)[j]
  ensures forall x :: x in RemoveDuplicates(sorted) ==> x in sorted
  ensures forall x :: x in sorted ==> x in RemoveDuplicates(sorted)
{
  if |sorted| == 0 then []
  else if |sorted| == 1 then sorted
  else
    var rest := RemoveDuplicates(sorted[1..]);
    if sorted[0] == rest[0] then rest
    else [sorted[0]] + rest
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
    sorted := [];
  } else {
    var pivot := s[|s|/2];
    var left : seq<int> := [];
    var right : seq<int> := [];
    
    var i := 0;
    while i < |s|
      invariant 0 <= i <= |s|
      invariant |left| + |right| == i
      invariant multiset(left) + multiset(right) == multiset(s[0..i])
      invariant forall x :: x in left ==> x <= pivot
      invariant forall x :: x in right ==> x >= pivot
    {
      if s[i] <= pivot {
        left := left + [s[i]];
      } else {
        right := right + [s[i]];
      }
      i := i + 1;
    }
    
    var sortedLeft := SortSeq(left);
    var sortedRight := SortSeq(right);
    sorted := sortedLeft + sortedRight;
  }
}
// </vc-code>

