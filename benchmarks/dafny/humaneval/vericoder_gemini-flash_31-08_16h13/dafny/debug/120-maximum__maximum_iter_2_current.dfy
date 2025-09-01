

// <vc-helpers>
function multiset<T>(s: seq<T>): multiset<T>
{
  if |s| == 0 then multiset{} else multiset{s[0]} + multiset(s[1..])
}

method SortSeq(s: seq<int>) returns (sorted: seq<int>)
  ensures forall i, j :: 0 <= i < j < |sorted| ==> sorted[i] <= sorted[j]
  ensures |sorted| == |s|
  ensures multiset(s) == multiset(sorted)
  ensures forall x :: x in s ==> x in sorted
  ensures forall x :: x in sorted ==> x in s
{
  sorted := s;
  var n := |sorted|;
  for i := 0 to n-2
    invariant 0 <= i < n
    invariant forall x, y :: (0 <= x < y <= i && y < n) ==> sorted[x] <= sorted[y]
    invariant multiset(s) == multiset(sorted)
  {
    for j := i+1 to n-1
      invariant i < j <= n
      invariant forall x, y :: (0 <= x < y <= i && y < n) ==> sorted[x] <= sorted[y]
      invariant forall x :: i <= x < j ==> sorted[i] <= sorted[x]
      invariant multiset(s) == multiset(sorted)
    {
      if sorted[j] < sorted[i]
      {
        sorted[i], sorted[j] := sorted[j], sorted[i];
      }
    }
  }
}
// </vc-helpers>

// <vc-spec>
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
// </vc-spec>
// <vc-code>
{
  var sorted_s := SortSeq(s);
  result := sorted_s[|sorted_s| - k ..];
}
// </vc-code>

method SortSeq(s: seq<int>) returns (sorted: seq<int>)
  ensures forall i, j :: 0 <= i < j < |sorted| ==> sorted[i] <= sorted[j]
  ensures |sorted| == |s|
  ensures multiset(s) == multiset(sorted)
  ensures forall i :: 0 <= i < |s| ==> exists j :: 0 <= j < |sorted| && s[i] == sorted[j]
  ensures forall x :: x in s ==> x in sorted
  ensures forall i :: 0 <= i < |s| ==> exists j :: 0 <= j < |sorted| && sorted[i] == s[j]
  ensures forall x :: x in sorted ==> x in s
{
  assume{:axiom} false;
}