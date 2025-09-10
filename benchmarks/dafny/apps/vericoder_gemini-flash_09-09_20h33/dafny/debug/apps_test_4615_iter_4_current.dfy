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
function max(x: int, y: int): int
{
  if x > y then x else y
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
    var best_total_mass := 0;
    var best_sugar_mass := 0;
    var best_density := -1;

    // Iterate through possible water mass contributions
    for i1 := 0 to 30 / a {
        for j1 := 0 to 30 / b {
            var water_units := a * i1 + b * j1;
            if water_units == 0 {
                continue;
            }
            var water_mass := water_units * 100;

            // Iterate through possible sugar mass contributions
            for i2 := 0 to 3000 / c {
                for j2 := 0 to 3000 / d {
                    var sugar_mass_candidate := c * i2 + d * j2;
                    // water_mass will always be > 0 here, so no need to check sugar_mass_candidate == 0 && water_mass == 0
                    
                    var total_mass_candidate := water_mass + sugar_mass_candidate;

                    if total_mass_candidate > f {
                        continue;
                    }

                    // Check sugar concentration constraint: sugar_mass <= water_units * e
                    if sugar_mass_candidate > water_units * e {
                        continue;
                    }

                    // Calculate density, handling total_mass_candidate == 0 case
                    var current_density := Density(total_mass_candidate, sugar_mass_candidate);

                    if current_density > best_density {
                        best_density := current_density;
                        best_total_mass := total_mass_candidate;
                        best_sugar_mass := sugar_mass_candidate;
                    } else if current_density == best_density {
                        if total_mass_candidate > best_total_mass {
                            best_total_mass := total_mass_candidate;
                            best_sugar_mass := sugar_mass_candidate;
                        }
                    }
                }
            }
        }
    }

    // The problem guarantees a solution exists, so best_total_mass will be > 0.
    // Smallest possible water_units is 1 (e.g., a=1, i1=1).
    // This results in water_mass of 100.
    // Given the constraints and problem definition, a valid solution will always be found.
    total_mass := best_total_mass;
    sugar_mass := best_sugar_mass;
}
// </vc-code>

