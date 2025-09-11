// <vc-preamble>
predicate IsOdd(n: int)
{
    n % 2 == 1
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method FindOddNumbers(arr: array<int>) returns (oddList: seq<int>)

    ensures forall i :: 0 <= i < |oddList| ==> IsOdd(oddList[i]) && oddList[i] in arr[..]

    ensures forall i :: 0 <= i < arr.Length && IsOdd(arr[i]) ==> arr[i] in oddList
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
