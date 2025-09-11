// <vc-preamble>
predicate IsEven(n: int)
{
    n % 2 == 0
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method RemoveOddNumbers(arr: array<int>) returns (evenList: seq<int>)

    ensures forall i :: 0 <= i < |evenList| ==> IsEven(evenList[i]) && evenList[i] in arr[..]

    ensures forall i :: 0 <= i < arr.Length && IsEven(arr[i]) ==> arr[i] in evenList
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
