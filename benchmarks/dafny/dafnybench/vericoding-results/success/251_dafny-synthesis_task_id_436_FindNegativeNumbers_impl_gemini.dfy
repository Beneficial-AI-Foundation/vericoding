// <vc-preamble>
predicate IsNegative(n: int)
{
    n < 0
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method FindNegativeNumbers(arr: array<int>) returns (negativeList: seq<int>)

    ensures forall i :: 0 <= i < |negativeList| ==> IsNegative(negativeList[i]) && negativeList[i] in arr[..]

    ensures forall i :: 0 <= i < arr.Length && IsNegative(arr[i]) ==> arr[i] in negativeList
// </vc-spec>
// <vc-code>
{
  negativeList := [];
  var i := 0;
  while i < arr.Length
    invariant 0 <= i <= arr.Length
    invariant forall j :: 0 <= j < |negativeList| ==> IsNegative(negativeList[j]) && negativeList[j] in arr[..i]
    invariant forall j :: 0 <= j < i && IsNegative(arr[j]) ==> arr[j] in negativeList
  {
    if IsNegative(arr[i]) {
      negativeList := negativeList + [arr[i]];
    }
    i := i + 1;
  }
}
// </vc-code>
