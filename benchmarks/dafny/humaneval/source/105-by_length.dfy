method SortReverseAndName(arr: seq<int>) returns (result: seq<string>)
  // post-conditions-start
  ensures |result| <= |arr|
  ensures forall i :: 0 <= i < |result| ==>
    result[i] in ["One", "Two", "Three", "Four", "Five", "Six", "Seven", "Eight", "Nine"]
  // post-conditions-end
{
  // impl-start
  var validNumbers := [];
  var i := 0;
  while i < |arr|
    // invariants-start
    invariant 0 <= i <= |arr|
    invariant |validNumbers| <= i
    invariant forall j :: 0 <= j < |validNumbers| ==> 1 <= validNumbers[j] <= 9
    // invariants-end
  {
    if 1 <= arr[i] <= 9 { validNumbers := validNumbers + [arr[i]]; }
    i := i + 1;
  }

  ghost var unsorted := validNumbers;
  validNumbers := SortSeq(validNumbers);
  // assert-start
  assert forall j :: 0 <= j < |validNumbers| ==> 1 <= validNumbers[j] <= 9 by {
    assert forall j :: 0 <= j < |validNumbers| ==> validNumbers[j] in multiset(unsorted);
  }
  // assert-end
  validNumbers := reverse(validNumbers);
  // assert-start
  assert forall j :: 0 <= j < |validNumbers| ==> 1 <= validNumbers[j] <= 9 by {
    assert forall j :: 0 <= j < |validNumbers| ==> validNumbers[j] in multiset(unsorted);
  }
  // assert-end

  assert forall i, j :: 0 <= i < j < |validNumbers| ==> validNumbers[i] >= validNumbers[j]; // assert-line
  result := [];
  i := 0;
  while i < |validNumbers|
    // invariants-start
    invariant 0 <= i <= |validNumbers|
    invariant |result| == i
    invariant forall j :: 0 <= j < i ==>
      result[j] in {"One", "Two", "Three", "Four", "Five", "Six", "Seven", "Eight", "Nine"}
    invariant forall j :: 0 <= j < |validNumbers| ==> 1 <= validNumbers[j] <= 9
    // invariants-end
  {
    result := result + [NumberToName(validNumbers[i])];
    i := i + 1;
  }
  // impl-end
}

method SortSeq(s: seq<int>) returns (sorted: seq<int>)
  // post-conditions-start
  ensures forall i, j :: 0 <= i < j < |sorted| ==> sorted[i] <= sorted[j]
  ensures |sorted| == |s|
  ensures multiset(s) == multiset(sorted)
  // post-conditions-end
{
  // impl-start
  sorted := s;
  var i := 0;
  while i < |sorted|
    // invariants-start
    invariant 0 <= i <= |sorted|
    invariant forall j, k :: 0 <= j < k < i ==> sorted[j] <= sorted[k]
    invariant multiset(s) == multiset(sorted)
    invariant forall j :: 0 <= j < i ==> forall k :: i <= k < |sorted| ==> sorted[j] <= sorted[k]
    invariant |sorted| == |s|
    // invariants-end
  {
    var minIndex := i;
    var j := i + 1;
    while j < |sorted|
      // invariants-start
      invariant i <= minIndex < j <= |sorted|
      invariant forall k :: i <= k < j ==> sorted[minIndex] <= sorted[k]
      // invariants-end
    {
      if sorted[j] < sorted[minIndex] {
        minIndex := j;
      }
      j := j + 1;
    }
    if minIndex != i {
      var temp := sorted[i];
      sorted := sorted[i := sorted[minIndex]][minIndex := temp];
    }
    i := i + 1;
  }
  // impl-end
}

method reverse(s: seq<int>) returns (rev: seq<int>)
  // post-conditions-start
  ensures |rev| == |s|
  ensures forall k :: 0 <= k < |s| ==> rev[k] == s[|s| - 1 - k]
  // post-conditions-end
{
  // impl-start
  rev := [];
  var i := 0;
  while (i < |s|)
    // invariants-start
    invariant i >= 0 && i <= |s|
    invariant |rev| == i
    invariant forall k :: 0 <= k < i ==> rev[k] == s[|s| - 1 - k]
    // invariants-end
  {
    rev := rev + [s[|s| - i - 1]];
    i := i + 1;
  }
  // impl-end
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
