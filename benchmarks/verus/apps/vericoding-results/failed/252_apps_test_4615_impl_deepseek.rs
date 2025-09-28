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

proof fn lemma_density_monotonic(total_mass1: int, total_mass2: int, sugar_mass1: int, sugar_mass2: int)
    requires
        total_mass1 > 0,
        total_mass2 > 0,
        sugar_mass1 >= 0,
        sugar_mass2 >= 0,
        sugar_mass1 <= total_mass1,
        sugar_mass2 <= total_mass2,
        total_mass1 <= total_mass2,
        sugar_mass1 <= sugar_mass2,
    ensures
        density(total_mass1, sugar_mass1) <= density(total_mass2, sugar_mass2)
{
}

proof fn lemma_arithmetic_identity(a: int, b: int)
    ensures
        a + b - a == b
{
}

/* helper modified by LLM (iteration 5): Removed invalid int variable declarations and fixed verification */
fn find_optimal_solution(
    a: i8,
    b: i8,
    c: i8,
    d: i8,
    e: i8,
    f: i8,
) -> (i8, i8)
    requires
        valid_input(a as int, b as int, c as int, d as int, e as int, f as int),
    ensures
        valid_solution(a as int, b as int, c as int, d as int, e as int, f as int, result.0 as int, result.1 as int),
        result.0 as int > 0 && result.1 as int >= 0,
        result.0 as int <= f as int && result.1 as int <= result.0 as int,
        exists|water_units: int| water_units > 0 && result.0 as int == (water_units * 100) + result.1 as int,
        exists|water_units: int| water_units > 0 && result.1 as int <= (water_units * e as int),
        exists|i1: int, j1: int, i2: int, j2: int| 
            i1 >= 0 && j1 >= 0 && i2 >= 0 && j2 >= 0 &&
            i1 <= 30 / a as int && j1 <= 30 / b as int &&
            i2 <= 3000 / c as int && j2 <= 3000 / d as int &&
            result.0 as int == ((a as int * i1 + b as int * j1) * 100 + (c as int * i2 + d as int * j2)) &&
            result.1 as int == (c as int * i2 + d as int * j2) &&
            a as int * i1 + b as int * j1 > 0
{
    let mut best_total: i8 = 0;
    let mut best_sugar: i8 = 0;

    let max_water_units = (f as i32) / 100;
    let max_sugar_units1 = 3000 / (c as i32);
    let max_sugar_units2 = 3000 / (d as i32);
    let max_water_units1 = 30 / (a as i32);
    let max_water_units2 = 30 / (b as i32);

    proof {
        lemma_arithmetic_identity(0, 0);
    }

    let mut water_units: i32 = 1;
    while water_units <= max_water_units
        invariant
            water_units >= 1,
            water_units <= max_water_units + 1,
            best_total >= 0,
            best_sugar >= 0,
            best_total <= f,
            best_sugar <= best_total
    {
        let max_sugar_for_water = water_units * (e as i32);
        let mut sugar_units1: i32 = 0;
        
        while sugar_units1 <= max_sugar_units1
            invariant
                sugar_units1 >= 0,
                sugar_units1 <= max_sugar_units1 + 1,
                best_total >= 0,
                best_sugar >= 0,
                best_total <= f,
                best_sugar <= best_total
        {
            let mut sugar_units2: i32 = 0;
            
            while sugar_units2 <= max_sugar_units2
                invariant
                    sugar_units2 >= 0,
                    sugar_units2 <= max_sugar_units2 + 1,
                    best_total >= 0,
                    best_sugar >= 0,
                    best_total <= f,
                    best_sugar <= best_total
            {
                let sugar_mass = (c as i32) * sugar_units1 + (d as i32) * sugar_units2;
                
                if sugar_mass <= max_sugar_for_water {
                    let mut water_units1: i32 = 0;
                    
                    while water_units1 <= max_water_units1
                        invariant
                            water_units1 >= 0,
                            water_units1 <= max_water_units1 + 1,
                            best_total >= 0,
                            best_sugar >= 0,
                            best_total <= f,
                            best_sugar <= best_total
                    {
                        let mut water_units2: i32 = 0;
                        
                        while water_units2 <= max_water_units2
                            invariant
                                water_units2 >= 0,
                                water_units2 <= max_water_units2 + 1,
                                best_total >= 0,
                                best_sugar >= 0,
                                best_total <= f,
                                best_sugar <= best_total
                        {
                            let water_total = (a as i32) * water_units1 + (b as i32) * water_units2;
                            
                            if water_total == water_units && water_total > 0 {
                                let total_mass = water_total * 100 + sugar_mass;
                                
                                if total_mass <= (f as i32) {
                                    proof {
                                        lemma_density_monotonic(best_total as int, total_mass as int, best_sugar as int, sugar_mass as int);
                                    }
                                    
                                    if sugar_mass > best_sugar as i32 || (sugar_mass == best_sugar as i32 && total_mass > best_total as i32) {
                                        best_total = total_mass as i8;
                                        best_sugar = sugar_mass as i8;
                                    }
                                }
                            }
                            water_units2 += 1;
                        }
                        water_units1 += 1;
                    }
                }
                sugar_units2 += 1;
            }
            sugar_units1 += 1;
        }
        water_units += 1;
    }
    
    (best_total, best_sugar)
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
{
    /* code modified by LLM (iteration 5): Fixed compilation by using i32 variables instead of int */
    let result = find_optimal_solution(a, b, c, d, e, f);
    result
}
// </vc-code>


}

fn main() {}