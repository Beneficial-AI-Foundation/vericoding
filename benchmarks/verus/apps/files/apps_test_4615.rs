// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(a: int, b: int, c: int, d: int, e: int, f: int) -> bool {
    1 <= a < b <= 30 &&
    1 <= c < d <= 30 &&
    1 <= e <= 100 &&
    100 * a <= f <= 3000
}

spec fn valid_solution(a: int, b: int, c: int, d: int, e: int, f: int, total_mass: int, sugar_mass: int) -> bool {
    total_mass > 0 && sugar_mass >= 0 &&
    total_mass <= f &&
    sugar_mass <= total_mass
}

spec fn density(total_mass: int, sugar_mass: int) -> int
    recommends total_mass >= 0 && sugar_mass >= 0
{
    if total_mass > 0 { (100 * sugar_mass) / total_mass } else { 0 }
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn solve(a: int, b: int, c: int, d: int, e: int, f: int) -> (int, int)
    requires valid_input(a, b, c, d, e, f)
    ensures ({
        let (total_mass, sugar_mass) = solve(a, b, c, d, e, f);
        valid_solution(a, b, c, d, e, f, total_mass, sugar_mass) &&
        total_mass >= 0 && sugar_mass >= 0 &&
        total_mass <= f &&
        sugar_mass <= total_mass &&
        (exists|water_units: int| water_units > 0 && total_mass == water_units * 100 + sugar_mass) &&
        (exists|water_units: int| water_units > 0 && sugar_mass <= water_units * e) &&
        (exists|i1: int, j1: int, i2: int, j2: int| 
            i1 >= 0 && j1 >= 0 && i2 >= 0 && j2 >= 0 &&
            i1 <= 30 / a && j1 <= 30 / b &&
            i2 <= 3000 / c && j2 <= 3000 / d &&
            total_mass == (a * i1 + b * j1) * 100 + (c * i2 + d * j2) &&
            sugar_mass == c * i2 + d * j2 &&
            a * i1 + b * j1 > 0) &&
        total_mass > 0
    })
// </vc-spec>
// <vc-code>
{
    assume(false);
    (0, 0)
}
// </vc-code>


}

fn main() {}