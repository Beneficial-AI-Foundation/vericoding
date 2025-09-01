method uniqueSorted(s: seq<int>) returns (result: seq<int>)
    // pre-conditions-start
    requires forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
    // pre-conditions-end
    // post-conditions-start
    ensures forall i, j :: 0 <= i < j < |result| ==> result[i] < result[j]
    ensures forall x :: x in result ==> x in s
    ensures forall x :: x in s ==> x in result
    // post-conditions-end
{
  assume{:axiom} false;
}
method unique(s: seq<int>) returns (result: seq<int>)
    // post-conditions-start
    ensures forall i, j :: 0 <= i < j < |result| ==> result[i] < result[j]
    ensures forall x :: x in result ==> x in s
    ensures forall x :: x in s ==> x in result
    // post-conditions-end
{
  assume{:axiom} false;
}

// <vc-helpers>
function InsertionSort(s: seq<int>): seq<int>
  decreases |s|
  ensures forall i, j :: 0 <= i < j < |InsertionSort(s)| ==> InsertionSort(s)[i] <= InsertionSort(s)[j]
  ensures |InsertionSort(s)| == |s|
  ensures multiset(InsertionSort(s)) == multiset(s)
{
  if |s| == 0 then
    s
  else
    var sorted_tail := InsertionSort(s[1..]);
    // The previous call ensures sorted_tail is sorted.
    // The multiset property is also preserved recursively.
    Insert(sorted_tail, s[0])
}

function Insert(s: seq<int>, x: int): seq<int>
  requires forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
  ensures forall i, j :: 0 <= i < j < |Insert(s,x)| ==> Insert(s,x)[i] <= Insert(s,x)[j]
  ensures |Insert(s,x)| == |s| + 1
  ensures multiset(Insert(s,x)) == multiset(s) + multiset{x}
{
  if |s| == 0 then
    [x]
  else if x <= s[0] then
    [x] + s
  else
    var inserted_tail := Insert(s[1..], x);
    // These assertions help Dafny to track the properties recursively.
    // The recursive call to `Insert` ensures `inserted_tail` is sorted and has the correct multiset.
    // We need to explicitly state that the remaining properties hold for the current method call.
    assert forall i, j :: 0 <= i < j < |inserted_tail| ==> inserted_tail[i] <= inserted_tail[j];
    assert multiset(inserted_tail) == multiset(s[1..]) + multiset{x};
    assert s[0] <= inserted_tail[0]; // Crucial for maintaining sorted order when appending s[0]
    [s[0]] + inserted_tail
}
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
  var result := InsertionSort(s);
  return result;
}
// </vc-code>

