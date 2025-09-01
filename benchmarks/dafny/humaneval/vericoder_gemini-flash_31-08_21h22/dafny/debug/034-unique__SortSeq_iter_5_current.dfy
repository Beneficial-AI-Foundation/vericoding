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
    assert forall i, j :: 0 <= i < j < |sorted_tail| ==> sorted_tail[i] <= sorted_tail[j];
    assert multiset(sorted_tail) == multiset(s[1..]);
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
    assert forall i, j :: 0 <= i < j < |inserted_tail| ==> inserted_tail[i] <= inserted_tail[j];
    assert multiset(inserted_tail) == multiset(s[1..]) + multiset{x};
    assert s[0] <= inserted_tail[0]; 
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

