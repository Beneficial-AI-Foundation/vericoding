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
function GetSortedIndex(i: int, len: int): int
    requires 0 <= i < len
    ensures 0 <= GetSortedIndex(i, len) < len
{
    if i % 2 == 0 then i / 2 else len - (i - 1) / 2 - 1
}

lemma StrangeMappingCorrect(s: seq<int>, sorted: seq<int>, strange: seq<int>)
    requires |s| == |sorted| == |strange|
    requires multiset(s) == multiset(sorted)
    requires forall i :: 0 <= i < |s| ==> strange[i] == sorted[GetSortedIndex(i, |s|)]
    ensures forall i :: 0 <= i < |s| && i % 2 == 0 ==> strange[i] == sorted[i / 2]
    ensures forall i :: 0 <= i < |s| && i % 2 == 1 ==> strange[i] == sorted[|s| - (i - 1) / 2 - 1]
{
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
    var sorted := SortSeq(s);
    var result: seq<int> := [];
    var i := 0;
    while i < |s|
        invariant 0 <= i <= |s|
        invariant |result| == i
        invariant forall j :: 0 <= j < i ==> result[j] == sorted[GetSortedIndex(j, |s|)]
    {
        result := result + [sorted[GetSortedIndex(i, |s|)]];
        i := i + 1;
    }
    StrangeMappingCorrect(s, sorted, result);
    return result;
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