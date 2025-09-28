// <vc-preamble>
function MultisetCount<T(==)>(s: seq<T>, x: T): nat
{
    |set i | 0 <= i < |s| && s[i] == x|
}
// </vc-preamble>

// <vc-helpers>
predicate Sorted(s: seq<int>) {
  forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
}

function Insert(x: int, s: seq<int>): seq<int>
  requires Sorted(s)
  ensures Sorted(Insert(x, s))
  ensures |Insert(x, s)| == |s| + 1
  ensures forall y :: MultisetCount(Insert(x, s), y) == MultisetCount(s, y) + (if y == x then 1 else 0)
  decreases |s|
{
  if |s| == 0 then
    [x]
  else if x <= s[0] then
    [x] + s
  else
    [s[0]] + Insert(x, s[1..])
}

function SortSeq(s: seq<int>): seq<int>
  ensures Sorted(SortSeq(s))
  ensures |SortSeq(s)| == |s|
  ensures forall y :: MultisetCount(SortSeq(s), y) == MultisetCount(s, y)
  decreases |s|
{
  if |s| == 0 then s
  else Insert(s[0], SortSeq(s[1..]))
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
  var t := SortSeq(s);
  result := new int[|t|];
  var i := 0;
  while i < |t|
    invariant 0 <= i <= |t|
    invariant result.Length == |t|
    invariant result[..i] == t[..i]
  {
    result[i] := t[i];
    i := i + 1;
  }
}
// </vc-code>
