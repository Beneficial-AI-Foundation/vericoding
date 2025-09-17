// <vc-preamble>
// ======= TASK =======
// Given two integers (positive, negative, or zero), return the product of their unit digits.
// The unit digit is the ones place digit of the absolute value of the number.

// ======= SPEC REQUIREMENTS =======
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
// ======= HELPERS =======
// </vc-helpers>

// <vc-spec>
method multiply(a: int, b: int) returns (result: int)
    ensures result == ProductOfUnitDigits(a, b)
    ensures ValidResult(result)
// </vc-spec>
// <vc-code>
{
    var unit_a := UnitDigit(a);
    var unit_b := UnitDigit(b);
    result := unit_a * unit_b;
}
// </vc-code>
