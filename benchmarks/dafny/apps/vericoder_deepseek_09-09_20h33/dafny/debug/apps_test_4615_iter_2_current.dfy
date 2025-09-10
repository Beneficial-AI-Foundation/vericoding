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
lemma SugarMassConstraint(total_mass: int, sugar_mass: int, e: int, water_units: int)
    requires total_mass > 0 && sugar_mass >= 0
    requires water_units > 0
    requires total_mass == water_units * 100 + sugar_mass
    ensures sugar_mass <= water_units * e
{
}

ghost method FindSolution(a: int, b: int, c: int, d: int, e: int, f: int) returns (total_mass: int, sugar_mass: int, water_units: int, i1: int, j1: int, i2: int, j2: int)
    requires ValidInput(a, b, c, d, e, f)
    ensures total_mass == (a * i1 + b * j1) * 100 + (c * i2 + d * j2)
    ensures sugar_mass == c * i2 + d * j2
    ensures a * i1 + b * j1 > 0
    ensures total_mass <= f
    ensures sugar_mass <= water_units * e
    ensures total_mass > 0 && sugar_mass >= 0
{
    var max_total_mass := f;
    var max_sugar_per_water := e;
    var best_total := 0;
    var best_sugar := 0;
    var best_i1 := 0;
    var best_j1 := 0;
    var best_i2 := 0;
    var best_j2 := 0;
    
    var max_i1 := 30 / a;
    var max_j1 := 30 / b;
    var max_i2 := 3000 / c;
    var max_j2 := 3000 / d;
    
    i1 := 0;
    while i1 <= max_i1
        invariant 0 <= i1 <= max_i1 + 1
    {
        j1 := 0;
        while j1 <= max_j1
            invariant 0 <= j1 <= max_j1 + 1
        {
            i2 := 0;
            while i2 <= max_i2
                invariant 0 <= i2 <= max_i2 + 1
            {
                j2 := 0;
                while j2 <= max_j2
                    invariant 0 <= j2 <= max_j2 + 1
                {
                    var current_water := a * i1 + b * j1;
                    var current_sugar := c * i2 + d * j2;
                    var current_total := current_water * 100 + current_sugar;
                    
                    if current_water > 0 && current_total <= f && current_sugar <= current_water * e {
                        if current_total > best_total || (current_total == best_total && current_sugar > best_sugar) {
                            best_total := current_total;
                            best_sugar := current_sugar;
                            best_i1 := i1;
                            best_j1 := j1;
                            best_i2 := i2;
                            best_j2 := j2;
                        }
                    }
                    j2 := j2 + 1;
                }
                i2 := i2 + 1;
            }
            j1 := j1 + 1;
        }
        i1 := i1 + 1;
    }
    
    total_mass := best_total;
    sugar_mass := best_sugar;
    water_units := best_i1 * a + best_j1 * b;
    i1 := best_i1;
    j1 := best_j1;
    i2 := best_i2;
    j2 := best_j2;
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
    ghost var water_units: int;
    ghost var i1: int, j1: int, i2: int, j2: int;
    total_mass, sugar_mass, water_units, i1, j1, i2, j2 := FindSolution(a, b, c, d, e, f);
    SugarMassConstraint(total_mass, sugar_mass, e, water_units);
}
// </vc-code>

