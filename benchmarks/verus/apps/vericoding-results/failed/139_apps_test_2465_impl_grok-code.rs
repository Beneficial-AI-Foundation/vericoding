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
/* helper modified by LLM (iteration 2): implementation of gcd spec function and executable gcd function with loop invariant */
spec fn gcd(a: int, b: int) -> int {
    if b == 0 { a } else { gcd(b, a % b) }
}

fn gcd_exec(a: i32, b: i32) -> i32 {
    let mut x = a;
    let mut y = b;
    while y != 0
        invariant
            gcd(x as int, y as int) == gcd(a as int, b as int),
    {
        let temp = x % y;
        x = y;
        y = temp;
    }
    x
}
// </vc-helpers>

// <vc-spec>
fn solve(angles: Vec<i8>) -> (result: Vec<i8>)
    requires valid_input(angles@.map(|i, x: i8| x as int))
    ensures correct_output(angles@.map(|i, x: i8| x as int), result@.map(|i, x: i8| x as int))
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): main loop to compute the result using gcd for each angle */
{
    let mut result: Vec<i8> = Vec::new();
    for i in 0..angles.len()
        invariant
            result.len() == i,
            forall|j: int| 0 <= j && j < i ==> #[trigger]result@[j] as int == compute_answer(angles@[j] as int),
    {
        let angle = angles[i] as i32;
        let g = gcd_exec(angle, 180);
        let de_over_g = angle / g;
        let n180_over_g = 180 / g;
        let ans = if de_over_g == n180_over_g - 1 { n180_over_g * 2 } else { n180_over_g };
        result.push(ans as i8);
    }
    result
}
// </vc-code>


}

fn main() {}