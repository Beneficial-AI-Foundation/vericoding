// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
predicate IsNegative(x: int) { x < 0 }

function AddIfNegativeDistinct(s: seq<int>, x: int): seq<int>
{
  if x < 0 && !(x in s) then s + [x] else s
}

lemma AddIfNegativeDistinct_preserves_neg(s: seq<int>, x: int)
  requires forall y :: y in s ==> y < 0
  ensures forall y :: y in AddIfNegativeDistinct(s, x) ==> y < 0
{
}

lemma AddIfNegativeDistinct_extends(s: seq<int>, x: int)
  ensures forall y :: y in s ==> y in AddIfNegativeDistinct(s, x)
{
}

lemma AddIfNegativeDistinct_covers_when_negative(s: seq<int>, x: int)
  ensures x < 0 ==> x in AddIfNegativeDistinct(s, x)
{
}
// </vc-helpers>

// <vc-spec>
method FindNegativeNumbers(arr: array<int>) returns (negative_list: seq<int>)
    ensures forall x :: x in negative_list ==> x < 0
    ensures forall i :: 0 <= i < arr.Length && arr[i] < 0 ==> arr[i] in negative_list
// </vc-spec>
// <vc-code>
{
  var res: seq<int> := [];
  var i: int := 0;
  while i < arr.Length
    invariant 0 <= i <= arr.Length
    invariant forall y :: y in res ==> y < 0
    invariant forall j :: 0 <= j < i && arr[j] < 0 ==> arr[j] in res
    decreases arr.Length - i
  {
    var oldRes := res;
    var x := arr[i];
    AddIfNegativeDistinct_preserves_neg(oldRes, x);
    AddIfNegativeDistinct_extends(oldRes, x);
    if x < 0 {
      AddIfNegativeDistinct_covers_when_negative(oldRes, x);
    }
    res := AddIfNegativeDistinct(oldRes, x);
    i := i + 1;
  }
  negative_list := res;
}
// </vc-code>
