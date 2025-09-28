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
/* helper modified by LLM (iteration 5): Fixed GCD to handle b=0 case and compute_answer_impl to handle overflow */
fn gcd_impl(a: u32, b: u32) -> (result: u32)
    requires
        a >= 1,
    ensures
        result >= 1,
        result <= a,
    decreases b
{
    if b == 0 {
        a
    } else {
        gcd_impl(b, a % b)
    }
}

fn compute_answer_impl(angle: i8) -> (result: i8)
    requires
        angle >= 1,
        angle < 180,
    ensures
        result as int == compute_answer(angle as int),
{
    let angle_u = angle as u32;
    let g = gcd_impl(angle_u, 180u32);
    let de_over_g = angle_u / g;
    let n180_over_g = 180u32 / g;
    
    assert(g >= 1);
    assert(g <= 180);
    assert(n180_over_g <= 180);
    
    if de_over_g + 1 == n180_over_g {
        assert(n180_over_g * 2 <= 360);
        (n180_over_g * 2) as i8
    } else {
        assert(n180_over_g <= 180);
        n180_over_g as i8
    }
}
// </vc-helpers>

// <vc-spec>
fn solve(angles: Vec<i8>) -> (result: Vec<i8>)
    requires valid_input(angles@.map(|i, x: i8| x as int))
    ensures correct_output(angles@.map(|i, x: i8| x as int), result@.map(|i, x: i8| x as int))
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed assert statement syntax */
    let mut result = Vec::new();
    let mut i = 0;
    
    while i < angles.len()
        invariant
            0 <= i <= angles.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result@[j] as int == compute_answer(angles@[j] as int),
            valid_input(angles@.map(|k, x: i8| x as int)),
        decreases angles.len() - i
    {
        let angle = angles[i];
        assert(angles@[i] as int >= 1 && angles@[i] as int < 180);
        assert(angle >= 1);
        assert(angle < 180);
        let answer = compute_answer_impl(angle);
        result.push(answer);
        i = i + 1;
    }
    
    result
}
// </vc-code>


}

fn main() {}