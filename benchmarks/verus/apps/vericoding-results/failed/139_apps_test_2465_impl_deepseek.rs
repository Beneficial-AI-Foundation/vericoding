// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(angles: Seq<int>) -> bool {
    forall|i: int| 0 <= i < angles.len() ==> #[trigger] angles[i] >= 1 && #[trigger] angles[i] < 180
}

spec fn gcd(a: int, b: int) -> int;

spec fn compute_answer(angle: int) -> int {
    let g = gcd(angle, 180int);
    let de_over_g = angle / g;
    let n180_over_g = 180int / g;
    if de_over_g == n180_over_g - 1 { n180_over_g * 2 } else { n180_over_g }
}

spec fn correct_output(angles: Seq<int>, result: Seq<int>) -> bool {
    valid_input(angles) ==> (
        result.len() == angles.len() &&
        forall|i: int| 0 <= i < angles.len() ==> #[trigger] result[i] == compute_answer(#[trigger] angles[i])
    )
}
// </vc-preamble>

// <vc-helpers>

proof fn gcd_properties(a: nat, b: nat, g: nat)
    requires
        g > 0,
        a % g == 0,
        b % g == 0,
        forall|d: nat| d > 0 && a % d == 0 && b % d == 0 ==> d <= g
    ensures
        g == gcd(a, b)
{
}

proof fn gcd_exists(a: nat, b: nat)
    ensures
        exists|g: nat| g > 0 && a % g == 0 && b % g == 0 && forall|d: nat| d > 0 && a % d == 0 && b % d == 0 ==> d <= g
{
}

spec fn gcd_spec(a: int, b: int) -> int
    decreases
        if a + b > 0 { a + b } else { 0 }
{
    if a > 0 && b > 0 {
        let g = gcd_spec(b % a, a);
        g
    } else if a > 0 {
        a
    } else if b > 0 {
        b
    } else {
        1
    }
}

proof fn gcd_equiv_spec(a: nat, b: nat)
    ensures
        gcd(a, b) == gcd_spec(a, b)
{
}

fn compute_gcd(a: nat, b: nat) -> (g: nat)
    requires
        a > 0,
        b > 0
    ensures
        g > 0,
        a % g == 0,
        b % g == 0,
        forall|d: nat| d > 0 && a % d == 0 && b % d == 0 ==> d <= g
    decreases
        if a < b { a } else { b }
{
    if a == b {
        a
    } else if a > b {
        compute_gcd(a - b, b)
    } else {
        compute_gcd(a, b - a)
    }
}

#[verus::uninterp]
spec fn gcd(a: int, b: int) -> int;

// </vc-helpers>

// <vc-spec>
fn solve(angles: Vec<i8>) -> (result: Vec<i8>)
    requires valid_input(angles@.map(|i, x: i8| x as int))
    ensures correct_output(angles@.map(|i, x: i8| x as int), result@.map(|i, x: i8| x as int))
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed ghost variable declaration syntax */
    let mut result = Vec::new();
    let mut i: usize = 0;

    while i < angles.len()
        invariant
            0 <= i <= angles.len(),
            result.len() == i,
            correct_output(angles@.map(|j, x: i8| x as int).subrange(0, i), result@.map(|j, x: i8| x as int))
    {
        let angle = angles[i];
        let angle_int: i32 = angle as i32;
        
        let g_val = compute_gcd(angle as nat, 180);
        
        ghost {
            let angle_int_ghost: int = angle as int;
            gcd_equiv_spec(angle as nat, 180);
            gcd_properties(angle as nat, 180, g_val);
            assert(g_val as int == gcd(angle_int_ghost, 180));
            assert(angle_int_ghost % (g_val as int) == 0);
            assert(180 % (g_val as int) == 0);
        }
        
        let de_over_g: i32 = angle_int / (g_val as i32);
        let n180_over_g: i32 = 180 / (g_val as i32);
        
        ghost {
            let angle_int_ghost: int = angle as int;
            let g_val_int: int = g_val as int;
            assert(de_over_g as int == angle_int_ghost / g_val_int);
            assert(n180_over_g as int == 180 / g_val_int);
        }
        
        let answer = if de_over_g == n180_over_g - 1 {
            n180_over_g * 2
        } else {
            n180_over_g
        };
        
        result.push(answer as i8);
        i += 1;
    }
    
    result
}
// </vc-code>


}

fn main() {}