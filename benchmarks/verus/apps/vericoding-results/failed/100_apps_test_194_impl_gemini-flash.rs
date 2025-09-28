// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(n: int, a: int, b: int, groups: Seq<int>) -> bool {
    n >= 1 && a >= 1 && b >= 1 && groups.len() == n &&
    forall|i: int| 0 <= i < groups.len() ==> groups[i] == 1 || groups[i] == 2
}

spec fn count_denied_people(groups: Seq<int>, a: int, b: int) -> int {
    count_denied_people_with_half(groups, a, b, 0)
}

spec fn count_denied_people_with_half(groups: Seq<int>, a: int, b: int, half_occupied: int) -> int
    decreases groups.len()
{
    if groups.len() == 0 {
        0
    } else {
        let group = groups[0];
        let rest = groups.subrange(1, groups.len() as int);
        if group == 2 {
            if b > 0 {
                count_denied_people_with_half(rest, a, b - 1, half_occupied)
            } else {
                2 + count_denied_people_with_half(rest, a, b, half_occupied)
            }
        } else {
            if a > 0 {
                count_denied_people_with_half(rest, a - 1, b, half_occupied)
            } else if b > 0 {
                count_denied_people_with_half(rest, a, b - 1, half_occupied + 1)
            } else if half_occupied > 0 {
                count_denied_people_with_half(rest, a, b, half_occupied - 1)
            } else {
                1 + count_denied_people_with_half(rest, a, b, half_occupied)
            }
        }
    }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): No helper modifications needed for this turn. */
// </vc-helpers>

// <vc-spec>
fn solve(n: i8, a: i8, b: i8, groups: Vec<i8>) -> (denied: i8)
    requires 
        valid_input(n as int, a as int, b as int, groups@.map_values(|x: i8| x as int))
    ensures 
        denied >= 0,
        denied as int == count_denied_people(groups@.map_values(|x: i8| x as int), a as int, b as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed type errors where `int` was being used for a `ghost` context by casting to `usize`, and ensured all spec variables were in `int` context. Adjusted the `denied_count` invariant to match the problem's definition more accurately regarding the total people denied. */
    let mut current_a = a;
    let mut current_b = b;
    let mut half_occupied = 0i8;
    let mut denied_count = 0i8;

    let groups_spec: Seq<int> = groups@.map_values(|x: i8| x as int);

    let mut i: i8 = 0;
    while (i as int) < groups_spec.len() // Use groups_spec.len() for int comparison
        invariant
            0 <= i as int,
            (i as int) <= groups_spec.len(),
            current_a as int <= a as int,
            current_b as int <= b as int,
            current_a >= 0,
            current_b >= 0,
            half_occupied >= 0,
            half_occupied <= n,
            denied_count as int == count_denied_people_with_half(
                groups_spec.subrange(0, i as int),
                a as int,
                b as int,
                0
            ) - count_denied_people_with_half(
                groups_spec.subrange(0, i as int),
                current_a as int,
                current_b as int,
                half_occupied as int
            )
    {
        let group = groups[i as usize];
        if group == 2i8 {
            if current_b > 0i8 {
                current_b = current_b - 1i8;
            } else {
                denied_count = denied_count + 2i8;
            }
        } else {
            if current_a > 0i8 {
                current_a = current_a - 1i8;
            } else if current_b > 0i8 {
                current_b = current_b - 1i8;
                half_occupied = half_occupied + 1i8;
            } else if half_occupied > 0i8 {
                half_occupied = half_occupied - 1i8;
            } else {
                denied_count = denied_count + 1i8;
            }
        }
        i = i + 1i8;
    }
    denied_count
}
// </vc-code>


}

fn main() {}