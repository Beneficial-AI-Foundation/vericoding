

// <vc-helpers>
function pred_third(i: int): bool {
  i % 3 == 0
}

method SortSeqPred(s: seq<int>, p: seq<bool>) returns (sorted: seq<int>)
  requires |s| == |p|
  ensures |sorted| == |s|
  ensures forall i, j :: 0 <= i < j < |sorted| && p[i] && p[j] ==> sorted[i] <= sorted[j]
  ensures multiset(s) == multiset(sorted)
  ensures forall i :: 0 <= i < |s| && !p[i] ==> sorted[i] == s[i]
{
  var n := |s|;
  var sorted_arr := new int[n];
  if n == 0 {
    return sorted_arr[..];
  }

  var indices_to_sort: seq<int> := [];
  for i := 0 to n-1 {
    if p[i] {
      indices_to_sort := indices_to_sort + [s[i]];
    }
  }

  indices_to_sort := Sort(indices_to_sort);

  var k := 0; // index for indices_to_sort
  for i := 0 to n-1 {
    if p[i] {
      sorted_arr[i] := indices_to_sort[k];
      k := k + 1;
    } else {
      sorted_arr[i] := s[i];
    }
  }
  return sorted_arr[..];
}

method Sort(a: seq<int>) returns (s: seq<int>)
  ensures |s| == |a|
  ensures forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
  ensures multiset(a) == multiset(s)
{
  var n := |a|;
  var s_arr := new int[n];
  if n == 0 {
    return s_arr[..];
  }

  var arr := new int[n];
  for i := 0 to n-1 {
    arr[i] := a[i];
  }

  for i := 1 to n-1 {
    var j := i;
    while j > 0 && arr[j-1] > arr[j]
      decreases j
    {
      arr[j-1], arr[j] := arr[j], arr[j-1];
      j := j - 1;
    }
  }

  for i := 0 to n-1 {
    s_arr[i] := arr[i];
  }
  return s_arr[..];
}
// </vc-helpers>

// <vc-spec>
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
// </vc-spec>
// <vc-code>
{
  var p_arr := new bool[|a|];
  for i := 0 to |a|-1 {
    p_arr[i] := pred_third(i);
  }
  sorted_even := SortSeqPred(a, p_arr[..]);
  return sorted_even;
}
// </vc-code>

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
{
  assume{:axiom} false;
}