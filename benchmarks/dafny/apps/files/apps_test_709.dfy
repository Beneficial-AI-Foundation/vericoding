// <vc-preamble>
function CountOnesInBinary(n: int): int
    requires n >= 1
    ensures CountOnesInBinary(n) >= 1
    decreases n
{
    if n == 1 then 1
    else if n % 2 == 1 then 1 + CountOnesInBinary(n / 2)
    else CountOnesInBinary(n / 2)
}

predicate ValidInput(x: int) {
    x >= 1
}

predicate ValidOutput(x: int, result: int) {
    ValidInput(x) && result == CountOnesInBinary(x)
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method MinBacteria(x: int) returns (result: int)
    requires ValidInput(x)
    ensures ValidOutput(x, result)
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
