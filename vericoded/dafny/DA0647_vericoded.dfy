predicate ValidInput(a: int, b: int, c: int, d: int, e: int, f: int)
{
    1 <= a < b <= 30 &&
    1 <= c < d <= 30 &&
    1 <= e <= 100 &&
    100 * a <= f <= 3000
}

predicate ValidSolution(a: int, b: int, c: int, d: int, e: int, f: int, total_mass: int, sugar_mass: int)
{
    total_mass > 0 && sugar_mass >= 0 &&
    total_mass <= f &&
    sugar_mass <= total_mass
}

function Density(total_mass: int, sugar_mass: int): int
    requires total_mass >= 0 && sugar_mass >= 0
{
    if total_mass > 0 then (100 * sugar_mass) / total_mass else 0
}

// <vc-helpers>
lemma DensityBounds(total_mass: int, sugar_mass: int)
    requires total_mass > 0 && sugar_mass >= 0 && sugar_mass <= total_mass
    ensures 0 <= Density(total_mass, sugar_mass) <= 100
{
    assert (100 * sugar_mass) / total_mass <= 100;
}

lemma WaterUnitsExist(i1: int, j1: int, i2: int, j2: int, a: int, b: int, c: int, d: int)
    requires i1 >= 0 && j1 >= 0 && i2 >= 0 && j2 >= 0
    requires a > 0 && b > 0 && c > 0 && d > 0
    requires a * i1 + b * j1 > 0
    ensures a * i1 + b * j1 > 0
{
}

lemma SugarConstraintSatisfied(a: int, e: int, sugar_mass: int)
    requires a >= 1 && e >= 1 && sugar_mass == 0
    ensures sugar_mass <= a * e
{
    assert 0 <= a * e;
}
// </vc-helpers>

// <vc-spec>
method solve(a: int, b: int, c: int, d: int, e: int, f: int) returns (total_mass: int, sugar_mass: int)
    requires ValidInput(a, b, c, d, e, f)
    ensures ValidSolution(a, b, c, d, e, f, total_mass, sugar_mass)
    ensures total_mass >= 0 && sugar_mass >= 0
    ensures total_mass <= f
    ensures sugar_mass <= total_mass
    ensures exists water_units :: water_units > 0 && total_mass == water_units * 100 + sugar_mass
    ensures exists water_units :: water_units > 0 && sugar_mass <= water_units * e
    ensures exists i1, j1, i2, j2 :: 
        i1 >= 0 && j1 >= 0 && i2 >= 0 && j2 >= 0 &&
        i1 <= 30 / a && j1 <= 30 / b &&
        i2 <= 3000 / c && j2 <= 3000 / d &&
        total_mass == (a * i1 + b * j1) * 100 + (c * i2 + d * j2) &&
        sugar_mass == c * i2 + d * j2 &&
        a * i1 + b * j1 > 0
    ensures total_mass > 0
// </vc-spec>
// <vc-code>
{
    var i1 := 1;
    var j1 := 0;
    var i2 := 0;
    var j2 := 0;
    
    var water_units := a * i1 + b * j1;
    sugar_mass := c * i2 + d * j2;
    total_mass := water_units * 100 + sugar_mass;
    
    assert water_units == a * 1 + b * 0 == a;
    assert water_units > 0;
    assert sugar_mass == 0;
    assert total_mass == a * 100;
    assert total_mass > 0;
    assert sugar_mass >= 0;
    assert sugar_mass <= total_mass;
    assert total_mass <= f;
    
    assert i1 >= 0 && j1 >= 0 && i2 >= 0 && j2 >= 0;
    assert i1 <= 30 / a && j1 <= 30 / b;
    assert i2 <= 3000 / c && j2 <= 3000 / d;
    assert total_mass == (a * i1 + b * j1) * 100 + (c * i2 + d * j2);
    assert sugar_mass == c * i2 + d * j2;
    assert a * i1 + b * j1 > 0;
    
    SugarConstraintSatisfied(a, e, sugar_mass);
    assert sugar_mass <= water_units * e;
}
// </vc-code>

