method SortReverseAndName(arr: seq<int>) returns (result: seq<string>)
  // post-conditions-start
  ensures |result| <= |arr|
  ensures forall i :: 0 <= i < |result| ==>
    result[i] in ["One", "Two", "Three", "Four", "Five", "Six", "Seven", "Eight", "Nine"]
  // post-conditions-end
{
  assume{:axiom} false;
}

// <vc-helpers>

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
  var arr := s;
  var n := |s|;
  for i := 0 to n
    invariant 0 <= i <= n
    invariant multiset(arr) == multiset(s)
    invariant forall j, k :: 0 <= j < k < i ==> arr[j] <= arr[k]
    invariant forall j :: 0 <= j < i ==> forall k :: i <= k < n ==> arr[j] <= arr[k]
  {
    var min := i;
    for j := i+1 to n
      invariant i+1 <= j <= n
      invariant forall k :: i <= k < j ==> arr[k] >= arr[min]
    {
      if arr[j] < arr[min] {
        min := j;
      }
    }
    arr := arr[i := arr[min], min := arr[i]];
  }
  return arr;
}
// </vc-code>

method reverse(s: seq<int>) returns (rev: seq<int>)
  // post-conditions-start
  ensures |rev| == |s|
  ensures forall k :: 0 <= k < |s| ==> rev[k] == s[|s| - 1 - k]
  // post-conditions-end
{
  assume{:axiom} false;
}
function NumberToName(n: int): string
  requires 1 <= n <= 9
{
  match n
  case 1 => "One"
  case 2 => "Two"
  case 3 => "Three"
  case 4 => "Four"
  case 5 => "Five"
  case 6 => "Six"
  case 7 => "Seven"
  case 8 => "Eight"
  case 9 => "Nine"
}
// pure-end