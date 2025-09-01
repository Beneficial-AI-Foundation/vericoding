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
function insert(x: int, s: seq<int>): (sorted: seq<int>)
  requires forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
  decreases |s|
  ensures forall i, j :: 0 <= i < j < |insert(x, s)| ==> insert(x, s)[i] <= insert(x, s)[j]
  ensures |insert(x, s)| == |s| + 1
  ensures multiset(insert(x, s)) == multiset(s) + multiset{x}
  ensures forall y :: y in insert(x, s) <==> y == x || y in s
{
  if |s| == 0 then [x]
  else if x <= s[0] then [x] + s
  else [s[0]] + insert(x, s[1..])
}

method SortSeq(s: seq<int>) returns (sorted: seq<int>)
  ensures forall i, j :: 0 <= i < j < |sorted| ==> sorted[i] <= sorted[j]
  ensures |sorted| == |s|
  ensures multiset(s) == multiset(sorted)
  ensures forall i :: 0 <= i < |s| ==> exists j :: 0 <= j < |sorted| && s[i] == sorted[j]
  ensures forall x :: x in s ==> x in sorted
  ensures forall x :: x in sorted ==> x in s
  ensures forall i :: 0 <= i < |s| ==> exists j :: 0 <= j < |sorted| && sorted[i] == s[j]
{
  var res := [];
  if |s| != 0 {
    var tail := SortSeq(s[1..]);
    res := insert(s[0], tail);
  }
  sorted := res;
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
  var sorted_seq := SortSeq(s);
  result := sorted_seq[|sorted_seq| - k ..];
}
// </vc-code>

