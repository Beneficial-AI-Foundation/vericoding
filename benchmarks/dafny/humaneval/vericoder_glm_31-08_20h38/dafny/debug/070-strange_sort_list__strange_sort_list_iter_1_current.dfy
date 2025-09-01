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
method SortSeq(s: seq<int>) returns (sorted: seq<int>)
  ensures forall i, j :: 0 <= i < j < |sorted| ==> sorted[i] <= sorted[j]
  ensures |sorted| == |s|
  ensures multiset(s) == multiset(sorted)
{
  if s == [] {
    return [];
  } else {
    var head, tail := s[0], s[1..];
    var sortedTail := SortSeq(tail);
    var i: int := 0;
    while i < |sortedTail| && sortedTail[i] < head
      invariant 0 <= i <= |sortedTail|
      invariant forall j :: 0 <= j < i ==> sortedTail[j] < head
      invariant forall j :: i <= j < |sortedTail| ==> head <= sortedTail[j]
    {
      i := i + 1;
    }
    return sortedTail[..i] + [head] + sortedTail[i..];
  }
}

method strange_sort_list_helper(s: seq<int>) returns (sorted: seq<int>, strange: seq<int>)
    ensures multiset(s) == multiset(sorted)
    ensures |s| == |sorted| == |strange|
    ensures forall i :: 0 <= i < |s| && i % 2 == 0 ==> strange[i] == sorted[i / 2]
    ensures forall i :: 0 <= i < |s| && i % 2 == 1 ==> strange[i] == sorted[|s| - (i - 1) / 2 - 1]
{
  sorted := SortSeq(s);
  strange := new int[|s|];
  var left, right := 0, |s| - 1;
  for i := 0 to |s| / 2
    invariant 0 <= left <= right < |s| + 1
    invariant left + i == right
    invariant left == i && right == |s| - i - 1
    invariant forall j :: 0 <= j < 2 * i ==> 
      (j % 2 == 0 ==> strange[j] == sorted[j / 2]) && 
      (j % 2 == 1 ==> strange[j] == sorted[|s| - (j - 1) / 2 - 1])
  {
    if left < right {
      strange[2 * i] := sorted[left];
      strange[2 * i + 1] := sorted[right];
    } else if left == right {
      strange[2 * i] := sorted[left];
    }
    left, right := left + 1, right - 1;
  }
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
  var _, strange := strange_sort_list_helper(s);
  return strange;
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