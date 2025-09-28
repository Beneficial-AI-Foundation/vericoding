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
/* helper modified by LLM (iteration 5): trivial_solution_exists lemma providing witnesses i1=1,j1=0,i2=0,j2=0 */
proof fn trivial_solution_exists(a: int, b: int, c: int, d: int, e: int, f: int)
    requires valid_input(a, b, c, d, e, f)
    ensures exists|i1:int, j1:int, i2:int, j2:int|
        i1 >= 0 && j1 >= 0 && i2 >= 0 && j2 >= 0 &&
        i1 <= 30int / a && j1 <= 30int / b &&
        i2 <= 3000int / c && j2 <= 3000int / d &&
        ((a * i1 + b * j1) * 100 + (c * i2 + d * j2)) == a * 100 &&
        (c * i2 + d * j2) == 0 &&
        a * i1 + b * j1 > 0
{
    proof {
        // witness i1=1, j1=0, i2=0, j2=0
        assert(a >= 1 && a <= 30);
        // 30int / a >= 1 because 1 <= a <= 30
        assert(1 <= 30int / a);
        assert(0 <= 30int / b);
        assert(0 <= 3000int / c);
        assert(0 <= 3000int / d);
        assert(((a * 1 + b * 0) * 100 + (c * 0 + d * 0)) == a * 100);
        assert((c * 0 + d * 0) == 0);
        assert(a * 1 + b * 0 > 0);
        // discharge the existential using the concrete witness
        assert(exists|i1:int, j1:int, i2:int, j2:int|
            i1 >= 0 && j1 >= 0 && i2 >= 0 && j2 >= 0 &&
            i1 <= 30int / a && j1 <= 30int / b &&
            i2 <= 3000int / c && j2 <= 3000int / d &&
            ((a * i1 + b * j1) * 100 + (c * i2 + d * j2)) == a * 100 &&
            (c * i2 + d * j2) == 0 &&
            a * i1 + b * j1 > 0);
    }
}

/* helper modified by LLM (iteration 5): one_unit_water helper returning water mass for given units */
spec fn one_unit_water(a: int) -> int {
    100 * a
}
// </vc-helpers>

// <vc-spec>
fn solve(a: i8, b: i8, c: i8, d: i8, e: i8, f: i8) -> (result: (i8, i8))
    requires valid_input(a as int, b as int, c as int, d as int, e as int, f as int)
    ensures ({
        let (total_mass, sugar_mass) = result;
        valid_solution(a as int, b as int, c as int, d as int, e as int, f as int, total_mass as int, sugar_mass as int) &&
        total_mass as int >= 0 && sugar_mass as int >= 0 &&
        total_mass as int <= f as int &&
        sugar_mass as int <= total_mass as int &&
        (exists|water_units: int| water_units > 0 && total_mass as int == #[trigger] (water_units * 100) + sugar_mass as int) &&
        (exists|water_units: int| water_units > 0 && sugar_mass as int <= #[trigger] (water_units * e as int)) &&
        (exists|i1: int, j1: int, i2: int, j2: int| 
            i1 >= 0 && j1 >= 0 && i2 >= 0 && j2 >= 0 &&
            i1 <= 30int / a as int && j1 <= 30int / b as int &&
            i2 <= 3000int / c as int && j2 <= 3000int / d as int &&
            total_mass as int == #[trigger] ((a as int * i1 + b as int * j1) * 100 + (c as int * i2 + d as int * j2)) &&
            sugar_mass as int == #[trigger] (c as int * i2 + d as int * j2) &&
            a as int * i1 + b as int * j1 > 0) &&
        total_mass as int > 0
    })
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): return trivial solution with i1=1,j1=0,i2=0,j2=0 and prove ensures */
{
    let total_mass_i32: i32 = ((a as i32 * 1 + b as i32 * 0) * 100) + (c as i32 * 0 + d as i32 * 0);
    let sugar_mass_i32: i32 = 0;
    proof {
        // establish the equalities linking runtime values to spec-level integers
        assert(total_mass_i32 as int == (a as int) * 100);
        assert(sugar_mass_i32 as int == 0);
        // positivity and bounds follow from the precondition valid_input
        assert(total_mass_i32 as int > 0);
        assert(total_mass_i32 as int <= f as int);
        assert(sugar_mass_i32 as int >= 0);
        assert(sugar_mass_i32 as int <= total_mass_i32 as int);
        // existence of water_units: choose water_units = a
        assert(a as int > 0);
        assert(total_mass_i32 as int == (a as int) * 100 + sugar_mass_i32 as int);
        assert(sugar_mass_i32 as int <= (a as int) * e as int);
        // provide concrete witnesses for i1, j1, i2, j2 = 1,0,0,0 and show predicate holds
        assert({
            let i1: int = 1;
            let j1: int = 0;
            let i2: int = 0;
            let j2: int = 0;
            i1 >= 0 && j1 >= 0 && i2 >= 0 && j2 >= 0 &&
            i1 <= 30int / (a as int) && j1 <= 30int / (b as int) &&
            i2 <= 3000int / (c as int) && j2 <= 3000int / (d as int) &&
            total_mass_i32 as int == ((a as int * i1 + b as int * j1) * 100 + (c as int * i2 + d as int * j2)) &&
            sugar_mass_i32 as int == (c as int * i2 + d as int * j2) &&
            a as int * i1 + b as int * j1 > 0
        });
        // discharge the existential using the established witness
        assert(exists|i1:int, j1:int, i2:int, j2:int|
            i1 >= 0 && j1 >= 0 && i2 >= 0 && j2 >= 0 &&
            i1 <= 30int / (a as int) && j1 <= 30int / (b as int) &&
            i2 <= 3000int / (c as int) && j2 <= 3000int / (d as int) &&
            total_mass_i32 as int == ((a as int * i1 + b as int * j1) * 100 + (c as int * i2 + d as int * j2)) &&
            sugar_mass_i32 as int == (c as int * i2 + d as int * j2) &&
            a as int * i1 + b as int * j1 > 0);
    }
    (total_mass_i32 as i8, sugar_mass_i32 as i8)
}

// </vc-code>


}

fn main() {}