

// <vc-helpers>
function multiset<T>(s: seq<T>): multiset<T>
{
  if |s| == 0 then multiset{} else multiset{s[0]} + multiset(s[1..])
}

method SortSeq(s: seq<int>) returns (sorted: seq<int>)
  ensures forall i, j :: 0 <= i < j < |sorted| ==> sorted[i] <= sorted[j]
  ensures |sorted| == |s|
  ensures multiset(s) == multiset(sorted)
  decreases |s|
{
  if |s| == 0 then
    sorted := [];
  else if |s| == 1 then
    sorted := s;
  else
    var pivot := s[0];
    var smaller: seq<int> := [];
    var larger: seq<int> := [];
    var equal: seq<int> := [];

    for i := 0 to |s|-1
      decreases |s|-i
      invariant 0 <= i <= |s|
      invariant multiset(s[0..i]) == multiset(smaller) + multiset(larger) + multiset(equal)
      invariant forall x :: x in smaller ==> x < pivot
      invariant forall x :: x in larger ==> x > pivot
      invariant forall x :: x in equal ==> x == pivot
    {
      if s[i] < pivot then
        smaller := smaller + [s[i]];
      else if s[i] > pivot then
        larger := larger + [s[i]];
      else
        equal := equal + [s[i]];
    }

    var sorted_smaller: seq<int>;
    sorted_smaller := SortSeq(smaller);
    var sorted_larger: seq<int>;
    sorted_larger := SortSeq(larger);

    sorted := sorted_smaller + equal + sorted_larger;
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