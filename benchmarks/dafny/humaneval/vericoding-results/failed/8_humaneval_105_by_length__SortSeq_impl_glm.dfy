// <vc-preamble>
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
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): Changed SeqToArray to method for side-effect safety */
method SeqToArray(s: seq<int>) returns (a: array<int>)
  ensures a.Length == |s|
  ensures forall i :: 0 <= i < |s| ==> a[i] == s[i]
{
  a := new int[|s|];
  for i := 0 to |s|-1 {
    a[i] := s[i];
  }
}

/* helper modified by LLM (iteration 5): Fixed array slice syntax and added reads clause */
function ArrayToSeq(a: array<int>): seq<int>
  reads a
{
  a[0..a.Length]
}
// </vc-helpers>

// <vc-spec>
method SortSeq(s: seq<int>) returns (sorted: seq<int>)

  ensures forall i, j :: 0 <= i < j < |sorted| ==> sorted[i] <= sorted[j]
  ensures |sorted| == |s|
  ensures multiset(s) == multiset(sorted)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Fixed array slice syntax in invariant */
{
  var arr := SeqToArray(s);
  var i := 0;
  while i < |arr|
    invariant 0 <= i <= |arr|
    invariant multiset(arr[0..arr.Length]) == multiset(s)
    invariant forall j, k :: 0 <= j < k < i ==> arr[j] <= arr[k]
    invariant forall j :: 0 <= j < i ==> forall k :: i <= k < |arr| ==> arr[j] <= arr[k]
  {
    var minIndex := i;
    var j := i + 1;
    while j < |arr|
      invariant i <= j <= |arr|
      invariant minIndex >= i && minIndex < |arr|
      invariant forall k :: i <= k < j ==> arr[minIndex] <= arr[k]
    {
      if arr[j] < arr[minIndex] {
        minIndex := j;
      }
      j := j + 1;
    }
    var temp := arr[i];
    arr[i] := arr[minIndex];
    arr[minIndex] := temp;
    i := i + 1;
  }

  sorted := ArrayToSeq(arr);
}
// </vc-code>
