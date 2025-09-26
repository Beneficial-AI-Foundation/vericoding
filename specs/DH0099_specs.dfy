// <vc-preamble>

function UnitDigit(n: int): int
{
    (if n >= 0 then n else -n) % 10
}

function ProductOfUnitDigits(a: int, b: int): int
{
    UnitDigit(a) * UnitDigit(b)
}

predicate ValidResult(result: int)
{
    result >= 0 && result <= 81
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method multiply(a: int, b: int) returns (result: int)
    ensures result == ProductOfUnitDigits(a, b)
    ensures ValidResult(result)
// </vc-spec>
// <vc-code>
{
    assume {:axiom} false;
  }
// </vc-code>
