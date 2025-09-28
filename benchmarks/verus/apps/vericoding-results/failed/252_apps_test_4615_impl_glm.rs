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
/* helper modified by LLM (iteration 5): Fixed type annotation in decreases clause */
fn compute_sugar_possible(c: i8, d: i8) -> (result: Vec<bool>)
    ensures
        result.len() == 3001,
        forall|s: int| 0 <= s < 3001 ==> #[trigger] result@[s] == exists|i: int, j: int|
            i >= 0 && j >= 0 && s == c as int * i + d as int * j,
{
    let mut sugar_possible = vec![false; 3001];
    let c_i32 = c as i32;
    let d_i32 = d as i32;
    
    let max_i2 = 3000 / c_i32;
    let max_j2 = 3000 / d_i32;
    
    for i2 in 0..(max_i2 + 1) {
        for j2 in 0..(max_j2 + 1) {
            let s = c_i32 * i2 + d_i32 * j2;
            if s <= 3000 {
                sugar_possible.set(s as usize, true);
            }
        }
    }
    sugar_possible
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
/* code modified by LLM (iteration 5): Fixed type annotation in decreases clause */
{
    let sugar_possible = compute_sugar_possible(c, d);
    
    let mut best_density = -1i32;
    let mut best_total = -1i32;
    let mut best_sugar = -1i32;

    let a_i32 = a as i32;
    let b_i32 = b as i32;
    let e_i32 = e as i32;
    let f_i32 = f as i32;
    
    for W in 1..=30 {
        let mut found_water = false;
        for i1 in 0..=(30/a_i32)
            decreases (30/a_i32 - i1) as int
        {
            for j1 in 0..=(30/b_i32)
                decreases (30/b_i32 - j1) as int
            {
                if a_i32 * i1 + b_i32 * j1 == W {
                    found_water = true;
                    break;
                }
            }
            if found_water { break; }
        }
        if !found_water {
            continue;
        }

        let max_sugar = (W * e_i32).min(3000).min(f_i32 - 100*W);
        if max_sugar < 0 {
            continue;
        }

        let mut S = max_sugar;
        let mut found_sugar = false;
        while S >= 0
            decreases S as int
        {
            if sugar_possible[S as usize] {
                found_sugar = true;
                break;
            }
            S = S - 1;
        }
        if found_sugar {
            let total_mass = 100 * W + S;
            let density = (S * 100) / total_mass;
            if density > best_density || (density == best_density && total_mass > best_total) {
                best_density = density;
                best_total = total_mass;
                best_sugar = S;
            }
        }
    }

    (best_total as i8, best_sugar as i8)
}
// </vc-code>


}

fn main() {}