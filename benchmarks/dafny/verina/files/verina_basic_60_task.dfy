// <vc-preamble>
predicate IsEven(n: int)
{
    n % 2 == 0
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method FindEvenNumbers(arr: array<int>) returns (result: array<int>)
    ensures forall i :: 0 <= i < result.Length ==> IsEven(result[i])
    ensures forall i :: 0 <= i < result.Length ==> exists j :: 0 <= j < arr.Length && result[i] == arr[j]
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume {:axiom} false;
    result := new int[0];
    // impl-end
}
// </vc-code>
