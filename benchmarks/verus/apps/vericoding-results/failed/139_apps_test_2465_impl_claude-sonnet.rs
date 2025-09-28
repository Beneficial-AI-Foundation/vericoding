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
spec fn gcd(a: int, b: int) -> int
    decreases if a >= b { a } else { b }
{
    if a == 0 {
        b
    } else if b == 0 {
        a
    } else if a >= b {
        gcd(a - b, b)
    } else {
        gcd(a, b - a)
    }
}

fn gcd_impl(a: i32, b: i32) -> (result: i32)
    requires a > 0, b > 0
    ensures result as int == gcd(a as int, b as int), result > 0
    decreases b
{
    if b == 0 {
        a
    } else {
        gcd_impl(b, a % b)
    }
}

fn compute_answer_impl(angle: i8) -> (result: i8)
    requires angle >= 1, angle < 180
    ensures result as int == compute_answer(angle as int)
{
    let g = gcd_impl(angle as i32, 180);
    let de_over_g = (angle as i32) / g;
    let n180_over_g = 180 / g;
    if de_over_g == n180_over_g - 1 {
        (n180_over_g * 2) as i8
    } else {
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
    /* code modified by LLM (iteration 5): use concrete types instead of int/nat */
    let mut result = Vec::new();
    let mut i = 0;
    while i < angles.len()
        invariant
            i <= angles.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result@[j] as int == compute_answer(angles@[j] as int)
    {
        let answer = compute_answer_impl(angles[i]);
        result.push(answer);
        i += 1;
    }
    result
}
// </vc-code>


}

fn main() {}