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
lemma ValidSolutionExists(a: int, b: int, c: int, d: int, e: int, f: int)
    requires ValidInput(a, b, c, d, e, f)
    ensures exists total_mass, sugar_mass ::
        ValidSolution(a, b, c, d, e, f, total_mass, sugar_mass) &&
        total_mass > 0 &&
        sugar_mass >= 0 &&
        total_mass <= f &&
        sugar_mass <= total_mass &&
        (exists water_units :: water_units > 0 && total_mass == water_units * 100 + sugar_mass) &&
        (exists water_units :: water_units > 0 && sugar_mass <= water_units * e) &&
        (exists i1, j1, i2, j2 :: 
            i1 >= 0 && j1 >= 0 && i2 >= 0 && j2 >= 0 &&
            i1 <= 30 / a && j1 <= 30 / b &&
            i2 <= 3000 / c && j2 <= 3000 / d &&
            total_mass == (a * i1 + b * j1) * 100 + (c * i2 + d * j2) &&
            sugar_mass == c * i2 + d * j2 &&
            a * i1 + b * j1 > 0)
{
    // Base case: just water, no sugar
    var total_mass := a * 100;
    var sugar_mass := 0;
    var water_units := a;
    assert water_units > 0;
    assert total_mass == water_units * 100 + sugar_mass;
    assert sugar_mass <= water_units * e;
    assert total_mass == (a * 1 + b * 0) * 100 + (c * 0 + d * 0);
    assert sugar_mass == c * 0 + d * 0;
    assert a * 1 + b * 0 > 0;
    assert ValidSolution(a, b, c, d, e, f, total_mass, sugar_mass);
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
    // Initialize with just water (a units)
    total_mass := a * 100;
    sugar_mass := 0;
    
    var i1 := 0;
    while i1 <= 30 / a && i1 <= 10
        invariant 0 <= i1 <= 11
        invariant total_mass > 0
        invariant sugar_mass >= 0
        invariant total_mass <= f
        invariant sugar_mass <= total_mass
    {
        var j1 := 0;
        while j1 <= 30 / b && j1 <= 10
            invariant 0 <= j1 <= 11
            invariant total_mass > 0
            invariant sugar_mass >= 0
            invariant total_mass <= f
            invariant sugar_mass <= total_mass
        {
            var water := a * i1 + b * j1;
            if water > 0 && water * 100 <= f {
                var i2 := 0;
                while i2 <= 3000 / c && i2 <= 10
                    invariant 0 <= i2 <= 11
                    invariant total_mass > 0
                    invariant sugar_mass >= 0
                    invariant total_mass <= f
                    invariant sugar_mass <= total_mass
                {
                    var j2 := 0;
                    while j2 <= 3000 / d && j2 <= 10
                        invariant 0 <= j2 <= 11
                        invariant total_mass > 0
                        invariant sugar_mass >= 0
                        invariant total_mass <= f
                        invariant sugar_mass <= total_mass
                    {
                        var sugar := c * i2 + d * j2;
                        var total := water * 100 + sugar;
                        
                        if total <= f && sugar <= water * e {
                            if sugar * total_mass <= sugar_mass * total {
                                // Skip update - current solution is better
                            } else {
                                total_mass := total;
                                sugar_mass := sugar;
                            }
                        }
                        j2 := j2 + 1;
                    }
                    i2 := i2 + 1;
                }
            }
            j1 := j1 + 1;
        }
        i1 := i1 + 1;
    }
}
// </vc-code>

