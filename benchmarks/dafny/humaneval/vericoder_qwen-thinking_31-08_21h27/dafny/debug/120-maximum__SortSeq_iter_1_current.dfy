method maximum(s: seq<int>, k: int) returns (result: seq<int>)
  // pre-conditions-start
  requires 1 <= k <= |s|
  requires 1 <= |s| <= 1000
  requires forall x :: x in s ==> -1000 <= x <= 1000
  // pre-conditions-end
  // post-conditions-start
  ensures |result| == k
  ensures forall i, j :: 0 <= i < j < k ==> result[i] <= result[j]
  ensures forall x :: x in result ==> x in s
  // post-conditions-end
{
  assume{:axiom} false;
}

// <vc-helpers>
predicate IsSorted(s: seq<int>) {
  forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
}

method Insert(x: int, s: seq<int>) returns (result: seq<int>)
  requires IsSorted(s)
  ensures IsSorted(result)
  ensures |result| == |s| + 1
  ensures multiset(result) == multiset(s) + {x}
  ensures exists i :: 0 <= i < |result| && result[i] == x
{
  if |s| == 0 {
    return [x];
  } else if x <= s[0] {
    return [x] + s;
  } else {
    return [s[0]] + Insert(x, s[1..]);
  }
}

method SortSeq(s: seq<int>) returns (sorted: seq<int>)
  ensures |sorted| == |s|
  ensures IsSorted(sorted)
  ensures multiset(s) == multiset(sorted)
{
  if |s| == 0 {
    return [];
  } else {
    var rest := s[1..];
    var sorted_rest := SortSeq(rest);
    return Insert(s[0], sorted_rest);
  }
}
// </vc-helpers>

// <vc-spec>
method SortSeq(s: seq<int>) returns (sorted: seq<int>)
  ensures forall i, j :: 0 <= i < j < |sorted| ==> sorted[i] <= sorted[j]
  ensures |sorted| == |s|
  ensures multiset(s) == multiset(sorted)
  ensures forall i :: 0 <= i < |s| ==> exists j :: 0 <= j < |sorted| && s[i] == sorted[j]
  ensures forall x :: x in s ==> x in sorted
  ensures forall i :: 0 <= i < |s| ==> exists j :: 0 <= j < |sorted| && sorted[i] == s[j]
  ensures forall x :: x in sorted ==> x in s
// </vc-spec>
// <vc-code>
{
  var sorted := SortSeq(s);
  return sorted[|s| - k .. |s|];
}
// </vc-code>

