predicate ValidInput(x: int, y: int, z: int)
{
    x >= 1 && y >= 1 && z >= 1 && y + 2 * z <= x
}

function MaxPeople(x: int, y: int, z: int): int
    requires ValidInput(x, y, z)
{
    (x - z) / (y + z)
}

predicate ValidSolution(x: int, y: int, z: int, result: int)
    requires ValidInput(x, y, z)
{
    result == MaxPeople(x, y, z) &&
    result >= 0 &&
    result * (y + z) <= x - z < (result + 1) * (y + z)
}

// <vc-helpers>
lemma DivisionProperty(dividend: int, divisor: int, quotient: int)
    requires divisor > 0
    requires quotient == dividend / divisor
    ensures quotient * divisor <= dividend < (quotient + 1) * divisor
{
    // This lemma captures the fundamental property of integer division
    // Dafny can prove this automatically
}

lemma MaxPeopleNonNegative(x: int, y: int, z: int)
    requires ValidInput(x, y, z)
    ensures MaxPeople(x, y, z) >= 0
{
    assert y + z >= 2; // Since y >= 1 and z >= 1
    assert x >= y + 2 * z; // From ValidInput
    assert x - z >= y + z; // Rearranging the above
    assert x - z >= 2; // Since y + z >= 2
    assert (x - z) / (y + z) >= 0; // Division of non-negative by positive
}
// </vc-helpers>

// <vc-spec>
method solve(x: int, y: int, z: int) returns (result: int)
    requires ValidInput(x, y, z)
    ensures ValidSolution(x, y, z, result)
// </vc-spec>
// <vc-code>
{
    result := (x - z) / (y + z);
    
    // Verify that result satisfies all conditions
    MaxPeopleNonNegative(x, y, z);
    assert result >= 0;
    
    DivisionProperty(x - z, y + z, result);
    assert result * (y + z) <= x - z < (result + 1) * (y + z);
}
// </vc-code>

