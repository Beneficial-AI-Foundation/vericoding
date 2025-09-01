

// <vc-helpers>
function method IsInValidRange(n: int): bool {
  1 <= n <= 9
}
// </vc-helpers>

// <vc-spec>
method SortReverseAndName(arr: seq<int>) returns (result: seq<string>)
  // post-conditions-start
  ensures |result| <= |arr|
  ensures forall i :: 0 <= i < |result| ==>
    result[i] in ["One", "Two", "Three", "Four", "Five", "Six", "Seven", "Eight", "Nine"]
  // post-conditions-end
// </vc-spec>
// <vc-code>
{
    var sortedArr := SortSeq(arr);
    var reversedArr := reverse(sortedArr);

    var tempResult: seq<string> := [];
    var i := 0;
    while i < |reversedArr|
      invariant 0 <= i <= |reversedArr|
      invariant |tempResult| == i
      invariant forall k :: 0 <= k < i ==> IsInValidRange(reversedArr[k]) ==>
                                             tempResult[k] == NumberToName(reversedArr[k])
      invariant forall k :: 0 <= k < i ==> !(IsInValidRange(reversedArr[k])) ==>
                                             tempResult[k] == "" // Placeholder if not valid
    {
        var num := reversedArr[i];
        if IsInValidRange(num) {
            tempResult := tempResult + [NumberToName(num)];
        }
        i := i + 1;
    }

    // Filter out empty strings if any, though with the current NumberToName and spec, they shouldn't occur
    // unless numbers outside 1-9 are present and would result in an "empty" name.
    // However, the postcondition implies only valid names will be in the result.
    // If numbers outside 1-9 are simply skipped, i.e., not included in 'result' at all.
    // Let's refine the filtering logic to only include valid names.

    var finalResult: seq<string> := [];
    var j := 0;
    while j < |tempResult|
      invariant 0 <= j <= |tempResult|
      invariant forall k :: 0 <= k < |finalResult| ==>
        finalResult[k] in ["One", "Two", "Three", "Four", "Five", "Six", "Seven", "Eight", "Nine"]
      invariant |finalResult| <= j
    {
      if tempResult[j] != "" { // Check if it's a valid name added from NumberToName
        finalResult := finalResult + [tempResult[j]];
      }
      j := j + 1;
    }

    return finalResult;
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