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
{
    /* code modified by LLM (iteration 5): Added decreases clauses to all loops */
    let mut best_total: i8 = 100;
    let mut best_sugar: i8 = 0;
    let mut best_density: i8 = 0;
    
    let mut i1: i8 = 0;
    while i1 <= 30 / a
        invariant
            0 <= i1 <= 30int / a as int + 1,
            valid_input(a as int, b as int, c as int, d as int, e as int, f as int),
            best_total >= 0,
            best_sugar >= 0,
            best_total as int <= f as int,
            best_sugar as int <= best_total as int,
            best_total > 0,
            exists|water_units: int| water_units > 0 && best_total as int == water_units * 100 + best_sugar as int,
            exists|water_units: int| water_units > 0 && best_sugar as int <= water_units * e as int,
            exists|ii1: int, jj1: int, ii2: int, jj2: int| 
                ii1 >= 0 && jj1 >= 0 && ii2 >= 0 && jj2 >= 0 &&
                ii1 <= 30int / a as int && jj1 <= 30int / b as int &&
                ii2 <= 3000int / c as int && jj2 <= 3000int / d as int &&
                best_total as int == (a as int * ii1 + b as int * jj1) * 100 + (c as int * ii2 + d as int * jj2) &&
                best_sugar as int == c as int * ii2 + d as int * jj2 &&
                a as int * ii1 + b as int * jj1 > 0,
            best_density as int == if best_total > 0 { (100 * best_sugar as int) / best_total as int } else { 0 },
        decreases 30int / a as int - i1 as int
    {
        let mut j1: i8 = 0;
        while j1 <= 30 / b
            invariant
                0 <= j1 <= 30int / b as int + 1,
                0 <= i1 <= 30int / a as int,
                valid_input(a as int, b as int, c as int, d as int, e as int, f as int),
                best_total >= 0,
                best_sugar >= 0,
                best_total as int <= f as int,
                best_sugar as int <= best_total as int,
                best_total > 0,
                exists|water_units: int| water_units > 0 && best_total as int == water_units * 100 + best_sugar as int,
                exists|water_units: int| water_units > 0 && best_sugar as int <= water_units * e as int,
                exists|ii1: int, jj1: int, ii2: int, jj2: int| 
                    ii1 >= 0 && jj1 >= 0 && ii2 >= 0 && jj2 >= 0 &&
                    ii1 <= 30int / a as int && jj1 <= 30int / b as int &&
                    ii2 <= 3000int / c as int && jj2 <= 3000int / d as int &&
                    best_total as int == (a as int * ii1 + b as int * jj1) * 100 + (c as int * ii2 + d as int * jj2) &&
                    best_sugar as int == c as int * ii2 + d as int * jj2 &&
                    a as int * ii1 + b as int * jj1 > 0,
                best_density as int == if best_total > 0 { (100 * best_sugar as int) / best_total as int } else { 0 },
            decreases 30int / b as int - j1 as int
        {
            let water_mass = (a * i1 + b * j1) * 100;
            if water_mass > 0 && water_mass <= f {
                let max_sugar = (a * i1 + b * j1) * e;
                
                let mut i2: i8 = 0;
                let max_i2 = if 100 / c < max_sugar / c { 100 / c } else { max_sugar / c };
                while i2 <= max_i2
                    invariant
                        0 <= i2 <= 127,
                        0 <= j1 <= 30int / b as int,
                        0 <= i1 <= 30int / a as int,
                        valid_input(a as int, b as int, c as int, d as int, e as int, f as int),
                        water_mass == (a * i1 + b * j1) * 100,
                        water_mass > 0,
                        water_mass <= f,
                        max_sugar == (a * i1 + b * j1) * e,
                        best_total >= 0,
                        best_sugar >= 0,
                        best_total as int <= f as int,
                        best_sugar as int <= best_total as int,
                        best_total > 0,
                        exists|water_units: int| water_units > 0 && best_total as int == water_units * 100 + best_sugar as int,
                        exists|water_units: int| water_units > 0 && best_sugar as int <= water_units * e as int,
                        exists|ii1: int, jj1: int, ii2: int, jj2: int| 
                            ii1 >= 0 && jj1 >= 0 && ii2 >= 0 && jj2 >= 0 &&
                            ii1 <= 30int / a as int && jj1 <= 30int / b as int &&
                            ii2 <= 3000int / c as int && jj2 <= 3000int / d as int &&
                            best_total as int == (a as int * ii1 + b as int * jj1) * 100 + (c as int * ii2 + d as int * jj2) &&
                            best_sugar as int == c as int * ii2 + d as int * jj2 &&
                            a as int * ii1 + b as int * jj1 > 0,
                        best_density as int == if best_total > 0 { (100 * best_sugar as int) / best_total as int } else { 0 },
                    decreases max_i2 as int - i2 as int
                {
                    let mut j2: i8 = 0;
                    let max_j2_sugar = if max_sugar - c * i2 >= 0 { (max_sugar - c * i2) / d } else { 0 };
                    let max_j2 = if 100 / d < max_j2_sugar { 100 / d } else { max_j2_sugar };
                    while j2 <= max_j2
                        invariant
                            0 <= j2 <= 127,
                            0 <= i2 <= 127,
                            0 <= j1 <= 30int / b as int,
                            0 <= i1 <= 30int / a as int,
                            valid_input(a as int, b as int, c as int, d as int, e as int, f as int),
                            water_mass == (a * i1 + b * j1) * 100,
                            water_mass > 0,
                            water_mass <= f,
                            max_sugar == (a * i1 + b * j1) * e,
                            best_total >= 0,
                            best_sugar >= 0,
                            best_total as int <= f as int,
                            best_sugar as int <= best_total as int,
                            best_total > 0,
                            exists|water_units: int| water_units > 0 && best_total as int == water_units * 100 + best_sugar as int,
                            exists|water_units: int| water_units > 0 && best_sugar as int <= water_units * e as int,
                            exists|ii1: int, jj1: int, ii2: int, jj2: int| 
                                ii1 >= 0 && jj1 >= 0 && ii2 >= 0 && jj2 >= 0 &&
                                ii1 <= 30int / a as int && jj1 <= 30int / b as int &&
                                ii2 <= 3000int / c as int && jj2 <= 3000int / d as int &&
                                best_total as int == (a as int * ii1 + b as int * jj1) * 100 + (c as int * ii2 + d as int * jj2) &&
                                best_sugar as int == c as int * ii2 + d as int * jj2 &&
                                a as int * ii1 + b as int * jj1 > 0,
                            best_density as int == if best_total > 0 { (100 * best_sugar as int) / best_total as int } else { 0 },
                        decreases max_j2 as int - j2 as int
                    {
                        let sugar_mass = c * i2 + d * j2;
                        let total_mass = water_mass + sugar_mass;
                        
                        if sugar_mass <= max_sugar && total_mass <= f {
                            let current_density = (100 * sugar_mass) / total_mass;
                            if current_density > best_density {
                                best_total = total_mass;
                                best_sugar = sugar_mass;
                                best_density = current_density;
                            }
                        }
                        j2 = j2 + 1;
                    }
                    i2 = i2 + 1;
                }
            }
            j1 = j1 + 1;
        }
        i1 = i1 + 1;
    }
    
    (best_total, best_sugar)
}
// </vc-code>


}

fn main() {}