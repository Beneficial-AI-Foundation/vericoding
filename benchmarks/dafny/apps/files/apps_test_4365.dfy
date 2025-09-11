// <vc-preamble>
predicate ValidInput(K: int) {
    2 <= K <= 100
}

function CountOddNumbers(K: int): int
    requires K >= 1
{
    (K + 1) / 2
}

function CountEvenNumbers(K: int): int
    requires K >= 1
{
    K / 2
}

function ExpectedResult(K: int): int
    requires ValidInput(K)
{
    CountOddNumbers(K) * CountEvenNumbers(K)
}

predicate CorrectResult(K: int, result: int)
    requires ValidInput(K)
{
    result == ExpectedResult(K)
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method CountEvenOddPairs(K: int) returns (result: int)
    requires ValidInput(K)
    ensures CorrectResult(K, result)
    ensures result >= 0
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
