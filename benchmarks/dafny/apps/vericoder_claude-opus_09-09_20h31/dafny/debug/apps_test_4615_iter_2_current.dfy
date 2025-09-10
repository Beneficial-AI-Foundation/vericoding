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
    var best_total := a * 100;
    var best_sugar := 0;
    
    // These witness the initial state
    ghost var witness_i1 := 1;
    ghost var witness_j1 := 0;
    ghost var witness_i2 := 0;
    ghost var witness_j2 := 0;
    ghost var witness_water := a;
    
    assert best_total == (a * witness_i1 + b * witness_j1) * 100 + (c * witness_i2 + d * witness_j2);
    assert best_sugar == c * witness_i2 + d * witness_j2;
    assert a * witness_i1 + b * witness_j1 > 0;
    assert witness_water > 0 && best_total == witness_water * 100 + best_sugar;
    assert witness_water > 0 && best_sugar <= witness_water * e;
    
    var i1 := 0;
    while i1 <= 30 / a
        invariant 0 <= i1 <= 30 / a + 1
        invariant best_total > 0
        invariant best_sugar >= 0
        invariant best_total <= f
        invariant best_sugar <= best_total
        invariant exists water_units :: water_units > 0 && best_total == water_units * 100 + best_sugar
        invariant exists water_units :: water_units > 0 && best_sugar <= water_units * e
        invariant exists ii1, jj1, ii2, jj2 :: 
            ii1 >= 0 && jj1 >= 0 && ii2 >= 0 && jj2 >= 0 &&
            ii1 <= 30 / a && jj1 <= 30 / b &&
            ii2 <= 3000 / c && jj2 <= 3000 / d &&
            best_total == (a * ii1 + b * jj1) * 100 + (c * ii2 + d * jj2) &&
            best_sugar == c * ii2 + d * jj2 &&
            a * ii1 + b * jj1 > 0
    {
        var j1 := 0;
        while j1 <= 30 / b
            invariant 0 <= j1 <= 30 / b + 1
            invariant best_total > 0
            invariant best_sugar >= 0
            invariant best_total <= f
            invariant best_sugar <= best_total
            invariant exists water_units :: water_units > 0 && best_total == water_units * 100 + best_sugar
            invariant exists water_units :: water_units > 0 && best_sugar <= water_units * e
            invariant exists ii1, jj1, ii2, jj2 :: 
                ii1 >= 0 && jj1 >= 0 && ii2 >= 0 && jj2 >= 0 &&
                ii1 <= 30 / a && jj1 <= 30 / b &&
                ii2 <= 3000 / c && jj2 <= 3000 / d &&
                best_total == (a * ii1 + b * jj1) * 100 + (c * ii2 + d * jj2) &&
                best_sugar == c * ii2 + d * jj2 &&
                a * ii1 + b * jj1 > 0
        {
            var water := a * i1 + b * j1;
            if water > 0 && water * 100 <= f {
                var i2 := 0;
                while i2 <= 3000 / c && i2 <= 100
                    invariant 0 <= i2 <= 3000 / c + 1
                    invariant 0 <= i2 <= 101
                    invariant best_total > 0
                    invariant best_sugar >= 0
                    invariant best_total <= f
                    invariant best_sugar <= best_total
                    invariant exists water_units :: water_units > 0 && best_total == water_units * 100 + best_sugar
                    invariant exists water_units :: water_units > 0 && best_sugar <= water_units * e
                    invariant exists ii1, jj1, ii2, jj2 :: 
                        ii1 >= 0 && jj1 >= 0 && ii2 >= 0 && jj2 >= 0 &&
                        ii1 <= 30 / a && jj1 <= 30 / b &&
                        ii2 <= 3000 / c && jj2 <= 3000 / d &&
                        best_total == (a * ii1 + b * jj1) * 100 + (c * ii2 + d * jj2) &&
                        best_sugar == c * ii2 + d * jj2 &&
                        a * ii1 + b * jj1 > 0
                {
                    var j2 := 0;
                    while j2 <= 3000 / d && j2 <= 100
                        invariant 0 <= j2 <= 3000 / d + 1
                        invariant 0 <= j2 <= 101
                        invariant best_total > 0
                        invariant best_sugar >= 0
                        invariant best_total <= f
                        invariant best_sugar <= best_total
                        invariant exists water_units :: water_units > 0 && best_total == water_units * 100 + best_sugar
                        invariant exists water_units :: water_units > 0 && best_sugar <= water_units * e
                        invariant exists ii1, jj1, ii2, jj2 :: 
                            ii1 >= 0 && jj1 >= 0 && ii2 >= 0 && jj2 >= 0 &&
                            ii1 <= 30 / a && jj1 <= 30 / b &&
                            ii2 <= 3000 / c && jj2 <= 3000 / d &&
                            best_total == (a * ii1 + b * jj1) * 100 + (c * ii2 + d * jj2) &&
                            best_sugar == c * ii2 + d * jj2 &&
                            a * ii1 + b * jj1 > 0
                    {
                        var sugar := c * i2 + d * j2;
                        var total := water * 100 + sugar;
                        
                        if total <= f && sugar <= water * e {
                            if best_total == 0 || (total > 0 && sugar * best_total > best_sugar * total) {
                                best_total := total;
                                best_sugar := sugar;
                                witness_i1 := i1;
                                witness_j1 := j1;
                                witness_i2 := i2;
                                witness_j2 := j2;
                                witness_water := water;
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
    
    total_mass := best_total;
    sugar_mass := best_sugar;
}
// </vc-code>

