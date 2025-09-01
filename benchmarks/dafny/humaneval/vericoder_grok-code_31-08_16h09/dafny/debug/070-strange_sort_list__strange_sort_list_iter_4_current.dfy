method strange_sort_list_helper(s: seq<int>) returns (sorted: seq<int>, strange: seq<int>)
    // post-conditions-start
    ensures multiset(s) == multiset(sorted)
    ensures |s| == |sorted| == |strange|
    ensures forall i :: 0 <= i < |s| && i % 2 == 0 ==> strange[i] == sorted[i / 2]
    ensures forall i :: 0 <= i < |s| && i % 2 == 1 ==> strange[i] == sorted[|s| - (i - 1) / 2 - 1]
    // post-conditions-end
{
  assume{:axiom} false;
}

// <vc-helpers>
method Insert(a: int, s: seq<int>) returns (r: seq<int>)
  requires forall i :: 0 <= i < |s|-1 ==> s[i] <= s[i+1]
  ensures multiset(r) == multiset([a] + s)
  ensures |r| == |s| + 1
  ensures forall i, j :: 0 <= i < j < |r| ==> r[i] <= r[j]
{
  if |s| == 0 || a <= s[0] {
    r := [a] + s;
  } else {
    var tailInserted := Insert(a, s[1..]);
    r := s[0..1] + tailInserted;
  }
}

method SortSeq(s: seq<int>) returns (sorted: seq<int>)
  ensures forall i, j :: 0 <= i < j < |sorted| ==> sorted[i] <= sorted[j]
  ensures |sorted| == |s|
  ensures multiset(s) == multiset(sorted)
{
  if |s| == 0 {
    sorted := [];
  } else {
    var tailSorted := SortSeq(s[1..]);
    var inserted := Insert(s[0], tailSorted);
    sorted := inserted;
  }
}

method strange_sort_list_helper(s: seq<int>) returns (sorted: seq<int>, strange: seq<int>)
  ensures multiset(s) == multiset(sorted)
  ensures |s| == |sorted| == |strange|
  ensures forall i :: 0 <= i < |s| && i % 2 == 0 ==> strange[i] == sorted[i / 2]
  ensures forall i :: 0 <= i < |s| && i % 2 == 1 ==> strange[i] == sorted[|s| - (i - 1) / 2 - 1]
{
  sorted := SortSeq(s);
  strange := seq(|s|, i => if i % 2 == 0 then sorted[i / 2] else sorted[|s| - (i - 1) / 2 - 1]);
}
// </vc-helpers>

// <vc-spec>
method strange_sort_list(s: seq<int>) returns (strange: seq<int>)
    // post-conditions-start
    ensures |s| == |strange|
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
  var sorted, tempStrange := strange_sort_list_helper(s);
  strange := tempStrange;
}
// </vc-code>

method SortSeq(s: seq<int>) returns (sorted: seq<int>)
  // post-conditions-start
  ensures forall i, j :: 0 <= i < j < |sorted| ==> sorted[i] <= sorted[j]
  ensures |sorted| == |s|
  ensures multiset(s) == multiset(sorted)
  // post-conditions-end
{
  assume{:axiom} false;
}