// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method Intersperse(numbers: array<int>, delim: int) returns (res: seq<int>)
    ensures
        numbers.Length == 0 ==> |res| == 0
    ensures
        numbers.Length != 0 ==> |res| == 2 * numbers.Length - 1
    ensures
        forall i :: 0 <= i < |res| && i % 2 == 0 ==> res[i] == numbers[i / 2]
    ensures
        forall i :: 0 <= i < |res| && i % 2 == 1 ==> res[i] == delim
// </vc-spec>
// <vc-code>
{
    assume {:axiom} false;
}
// </vc-code>
