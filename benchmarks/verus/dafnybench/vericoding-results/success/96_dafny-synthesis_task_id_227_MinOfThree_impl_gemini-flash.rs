use vstd::prelude::*;

verus! {

// <vc-helpers>
fn min_of_two(a: i32, b: i32) -> (min: i32)
    ensures
        min <= a && min <= b,
        (min == a) || (min == b),
{
    if a < b { a } else { b }
}
// </vc-helpers>

// <vc-spec>
fn min_of_three(a: i32, b: i32, c: i32) -> (min: i32)
    ensures
        min <= a && min <= b && min <= c,
        (min == a) || (min == b) || (min == c),
// </vc-spec>
// <vc-code>
{
    let min_ab = min_of_two(a, b);
    let min_abc = min_of_two(min_ab, c);
    min_abc
}
// </vc-code>

fn main() {
}

}