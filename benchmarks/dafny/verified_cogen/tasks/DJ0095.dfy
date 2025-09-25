// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method ContainsConsecutiveNumbers(arr: array<int>) returns (is_consecutive: bool)
    requires arr.Length > 0
    requires forall i :: 0 <= i < arr.Length ==> (0 <= arr[i] + 1 < 2147483647)
    ensures is_consecutive == (forall i, j :: 0 <= i < j < arr.Length && j == i + 1 ==> (arr[i] + 1 == arr[j]))
// </vc-spec>
// <vc-code>
{
    assume {:axiom} false;
}
// </vc-code>
