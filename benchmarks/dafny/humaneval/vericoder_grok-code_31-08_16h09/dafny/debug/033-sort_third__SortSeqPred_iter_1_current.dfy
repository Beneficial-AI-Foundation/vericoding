method sort_third(a: seq<int>) returns (sorted_even: seq<int>)
  // pre-conditions-start
  requires |a| > 0
  // pre-conditions-end
  // post-conditions-start
  ensures |sorted_even| == |a|
  ensures forall i, j :: 0 <= i < j < |sorted_even| && i % 3 == 0 && j % 3 == 0 ==>
      sorted_even[i] <= sorted_even[j]
  ensures forall i :: 0 <= i < |a| && i % 3 != 0 ==> sorted_even[i] == a[i]
  ensures multiset(a) == multiset(sorted_even)
  // post-conditions-end
{
  assume{:axiom} false;
}

// <vc-helpers>
function Sorted(s: seq<int>): bool {
  forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
}

function Insert(x: int, s: seq<int>): seq<int>
  decreases |s|
  requires Sorted(s)
  ensures |result| == |s| + 1
  ensures multiset(result) == multiset(s) + multiset{x}
  ensures Sorted(result)
{
  if |s| == 0 {
    [x]
  } else if x <= s[0] {
    [x] + s
  } else {
    [s[0]] + Insert(x, s[1..])
  }
}

function ISort(s: seq<int>): seq<int>
  ensures |result| == |s|
  ensures multiset(result) == multiset(s)
  ensures Sorted(result)
{
  if |s| == 0 {
    []
  } else {
    Insert(s[0], ISort(s[1..]))
  }
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
  var to_sort: seq<int> := [];
  var k: int := 0;
  while k < |s|
  {
    if p[k] {
      to_sort := to_sort + [s[k]];
    }
    k := k + 1;
  }
  var sorted_to_sort: seq<int> := ISort(to_sort);
  var result: seq<int> := [];
  var l: int := 0;
  var m: int := 0;
  while m < |s|
  {
    if !p[m] {
      result := result + [s[m]];
    } else {
      result := result + [sorted_to_sort[l]];
      l := l + 1;
    }
    m := m + 1;
  }
  sorted := result;
}
// </vc-code>

