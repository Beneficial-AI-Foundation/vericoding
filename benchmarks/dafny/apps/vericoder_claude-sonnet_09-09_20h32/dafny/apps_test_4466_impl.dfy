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
lemma DivisionProperties(x: int, y: int, z: int)
    requires ValidInput(x, y, z)
    ensures var q := (x - z) / (y + z);
            q >= 0 &&
            q * (y + z) <= x - z < (q + 1) * (y + z)
{
    var numerator := x - z;
    var denominator := y + z;
    
    assert denominator > 0 by {
        assert y >= 1 && z >= 1;
    }
    
    assert numerator >= 0 by {
        assert y + 2 * z <= x;
        assert z >= 1;
        assert y + z <= y + 2 * z - z;
        assert y + z <= x - z;
        assert numerator >= y + z >= 2;
    }
    
    var q := numerator / denominator;
    assert q >= 0;
    assert q * denominator <= numerator < (q + 1) * denominator;
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
    DivisionProperties(x, y, z);
}
// </vc-code>

