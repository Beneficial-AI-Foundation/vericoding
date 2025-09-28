// <vc-preamble>
function MultisetCount<T(==)>(s: seq<T>, x: T): nat
{
    |set i | 0 <= i < |s| && s[i] == x|
}
// </vc-preamble>

// <vc-helpers>
function IsSorted(s: seq<int>): bool
{
  forall i, j | 0 <= i < j < |s| :: s[i] <= s[j]
}

function InsertIntoSorted(sorted: seq<int>, x: int): seq<int>
  requires IsSorted(sorted)
  ensures IsSorted(InsertIntoSorted(sorted, x))
  ensures forall x' :: MultisetCount(sorted + [x], x') == MultisetCount(InsertIntoSorted(sorted, x), x')
  ensures |sorted + [x]| == |InsertIntoSorted(sorted, x)|
{
  if |sorted| == 0 then [x]
  else if x <= sorted[0] then [x] + sorted
  else [sorted[0]] + InsertIntoSorted(sorted[1..], x)
}

function SortSeq(s: seq<int>): seq<int>
  ensures IsSorted(SortSeq(s))
  ensures forall x :: MultisetCount(s, x) == MultisetCount(SortSeq(s), x)
  ensures |s| == |SortSeq(s)|
{
  if |s| == 0 then []
  else InsertIntoSorted(SortSeq(s[1..]), s[0])
}

// </vc-helpers>

// <vc-spec>
method Sort(a: array<int>) returns (result: array<int>)
    ensures
        result.Length == a.Length &&
        (forall i, j :: 0 <= i < j < result.Length ==> result[i] <= result[j]) &&
        (forall x :: MultisetCount(result[..], x) == MultisetCount(a[..], x))
// </vc-spec>
// <vc-code>
{
  var s := a[..];
  var sortedS := SortSeq(s);
  result := new int[a.Length];
  var i := 0;
  while i < a.Length
    invariant 0 <= i <= a.Length
  {
    result[i] := sortedS[i];
    i := i + 1;
  }
}
// </vc-code>
