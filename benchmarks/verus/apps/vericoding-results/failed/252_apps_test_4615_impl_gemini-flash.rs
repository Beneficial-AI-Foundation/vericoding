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
/* code modified by LLM (iteration 5): Corrected several errors including integer overflow potential, off-by-one errors in loop conditions, and updated loop invariants. */
{
    let mut best_total_mass: i32 = 0;
    let mut best_sugar_mass: i32 = 0;
    let mut max_density: i32 = -1; // Represents the best 100*sugar_mass/total_mass

    let mut i1: i32 = 0; // Number of 'a' water units
    while i1 * (a as i32) * 100 <= (f as i32) && i1 * (a as i32) <= 30
        invariant
            a >= 1, b >= 1, c >= 1, d >= 1, e >= 1, f >= 100 * a,
            max_density >= -1,
            (max_density == -1) ==> (best_total_mass == 0 && best_sugar_mass == 0),
            (max_density != -1) ==> (best_total_mass > 0 && best_sugar_mass >= 0 && (
                best_total_mass <= f as i32 && best_sugar_mass <= best_total_mass
            )),
            i1 >= 0,
            i1 * (a as i32) >= 0,
            i1 * (a as i32) <= 30,
        decreases (30 - (i1 * (a as i32))) as int
    {
        let mut j1: i32 = 0; // Number of 'b' water units
        while (i1 * (a as i32) + j1 * (b as i32)) * 100 <= (f as i32) && (i1 * (a as i32) + j1 * (b as i32)) <= 30
            invariant
                a >= 1, b >= 1, c >= 1, d >= 1, e >= 1, f >= 100 * a,
                max_density >= -1,
                (max_density == -1) ==> (best_total_mass == 0 && best_sugar_mass == 0),
                (max_density != -1) ==> (best_total_mass > 0 && best_sugar_mass >= 0 && (
                    best_total_mass <= f as i32 && best_sugar_mass <= best_total_mass
                )),
                i1 >= 0, i1 * (a as i32) <= 30, (i1 * (a as i32)) * 100 <= (f as i32), // From outer loop
                j1 >= 0,
                (i1 * (a as i32) + j1 * (b as i32)) >= 0,
                (i1 * (a as i32) + j1 * (b as i32)) <= 30,
                (i1 * (a as i32) + j1 * (b as i32)) * 100 <= (f as i32)
            decreases (30 - (i1 * (a as i32) + j1 * (b as i32))) as int
        {
            let water_units_val = i1 * (a as i32) + j1 * (b as i32);
            if water_units_val > 0 {
                let max_sugar_mass = water_units_val * (e as i32);

                let mut current_sugar_mass_accumulator: i32 = 0;
                let mut i2: i32 = 0;
                while current_sugar_mass_accumulator <= max_sugar_mass && (water_units_val * 100 + current_sugar_mass_accumulator) <= (f as i32) && current_sugar_mass_accumulator <= 3000
                    invariant
                        a >= 1, b >= 1, c >= 1, d >= 1, e >= 1, f >= 100 * a,
                        max_density >= -1,
                        (max_density == -1) ==> (best_total_mass == 0 && best_sugar_mass == 0),
                        (max_density != -1) ==> (best_total_mass > 0 && best_sugar_mass >= 0 && (
                            best_total_mass <= f as i32 && best_sugar_mass <= best_total_mass
                        )),
                        i1 >= 0, i1 * (a as i32) <= 30, (i1 * (a as i32)) * 100 <= (f as i32),
                        j1 >= 0, (i1 * (a as i32) + j1 * (b as i32)) <= 30, ((i1 * (a as i32) + j1 * (b as i32))) * 100 <= (f as i32),
                        water_units_val == i1 * (a as i32) + j1 * (b as i32),
                        water_units_val > 0,
                        max_sugar_mass == water_units_val * (e as i32),
                        i2 >= 0,
                        current_sugar_mass_accumulator == i2 * (c as i32),
                        current_sugar_mass_accumulator >= 0,
                    decreases max_sugar_mass - current_sugar_mass_accumulator as int
                {
                    let mut j2: i32 = 0;
                    while (current_sugar_mass_accumulator + j2 * (d as i32)) <= max_sugar_mass && (water_units_val * 100 + current_sugar_mass_accumulator + j2 * (d as i32)) <= (f as i32) && (current_sugar_mass_accumulator + j2 * (d as i32)) <= 3000
                        invariant
                            a >= 1, b >= 1, c >= 1, d >= 1, e >= 1, f >= 100 * a,
                            max_density >= -1,
                            (max_density == -1) ==> (best_total_mass == 0 && best_sugar_mass == 0),
                            (max_density != -1) ==> (best_total_mass > 0 && best_sugar_mass >= 0 && (
                                best_total_mass <= f as i32 && best_sugar_mass <= best_total_mass
                            )),
                            i1 >= 0, i1 * (a as i32) <= 30, (i1 * (a as i32)) * 100 <= (f as i32),
                            j1 >= 0, (i1 * (a as i32) + j1 * (b as i32)) <= 30, ((i1 * (a as i32) + j1 * (b as i32))) * 100 <= (f as i32),
                            water_units_val == i1 * (a as i32) + j1 * (b as i32),
                            water_units_val > 0,
                            max_sugar_mass == water_units_val * (e as i32),
                            i2 >= 0, current_sugar_mass_accumulator == i2 * (c as i32),
                            current_sugar_mass_accumulator >= 0,
                            j2 >= 0, j2 * (d as i32) >= 0,
                            (current_sugar_mass_accumulator + j2 * (d as i32)) <= max_sugar_mass,
                            (water_units_val * 100 + current_sugar_mass_accumulator + j2 * (d as i32)) <= (f as i32),
                            (current_sugar_mass_accumulator + j2 * (d as i32)) <= 3000,
                        decreases max_sugar_mass - (current_sugar_mass_accumulator + j2 * (d as i32))
                    {
                        let sugar_mass_val = current_sugar_mass_accumulator + j2 * (d as i32);
                        let total_mass_val = water_units_val * 100 + sugar_mass_val;

                        if total_mass_val <= (f as i32) && total_mass_val > 0 {
                            let current_density = (100 * sugar_mass_val) / total_mass_val;

                            if current_density > max_density {
                                max_density = current_density;
                                best_total_mass = total_mass_val;
                                best_sugar_mass = sugar_mass_val;
                            }
                        }
                        j2 = j2 + 1;
                    }
                    i2 = i2 + 1;
                    current_sugar_mass_accumulator = i2 * (c as i32);
                }
            }
            j1 = j1 + 1;
        }
        i1 = i1 + 1;
    }

    (best_total_mass as i8, best_sugar_mass as i8)
}
// </vc-code>


}

fn main() {}