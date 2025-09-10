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
lemma MaxPeopleProperty(x: int, y: int, z: int, result: int)
    requires ValidInput(x, y, z)
    requires result == MaxPeople(x, y, z)
    ensures result >= 0
    ensures result * (y + z) <= x - z < (result + 1) * (y + z)
{
    // The properties follow from the definition of integer division
    // and the fact that y + z > 0 (since y >= 1, z >= 1)
    var divisor := y + z;
    var dividend := x - z;
    
    // Since divisor >= 2 (y>=1, z>=1) and dividend >= 0 (x>=y+2z => x-z>=y+z>=2)
    // Integer division properties guarantee:
    // result * divisor <= dividend < (result + 1) * divisor
}

lemma DivisionProperties(a: int, b: int)
    requires a >= 0
    requires b >= 1
    ensures a / b >= 0
    ensures a / b * b <= a < (a / b + 1) * b
{
    // Standard properties of integer division
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
    assert result >= 0 by {
        DivisionProperties(x - z, y + z);
    }
    assert result * (y + z) <= x - z < (result + 1) * (y + z) by {
        DivisionProperties(x - z, y + z);
    }
}
// </vc-code>

