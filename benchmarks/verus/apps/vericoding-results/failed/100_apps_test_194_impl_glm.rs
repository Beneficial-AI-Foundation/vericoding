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
fn count_denied_recursive(
    groups: &Vec<i8>,
    start: usize,
    a_remaining: i8,
    b_remaining: i8,
    half_occupied: i8,
) -> (denied: i8)
    requires 
        a_remaining >= 0 && b_remaining >= 0 && half_occupied >= 0,
        start <= groups.len(),
        forall|i: int| start <= i < groups.len() ==> groups@[i] == 1 || groups@[i] == 2
    ensures 
        denied >= 0,
        denied as int == count_denied_people_with_half(
            groups@.subrange(start as int, groups.len() as int).map_values(|x: i8| x as int),
            a_remaining as int,
            b_remaining as int,
            half_occupied as int
        )
    decreases groups.len() - start
{
    if start == groups.len() {
        0
    } else {
        let group = groups[start];
        let rest_start = start + 1;
        if group == 2 {
            if b_remaining > 0 {
                count_denied_recursive(groups, rest_start, a_remaining, b_remaining - 1, half_occupied)
            } else {
                2 + count_denied_recursive(groups, rest_start, a_remaining, b_remaining, half_occupied)
            }
        } else {
            if a_remaining > 0 {
                count_denied_recursive(groups, rest_start, a_remaining - 1, b_remaining, half_occupied)
            } else if b_remaining > 0 {
                count_denied_recursive(groups, rest_start, a_remaining, b_remaining - 1, half_occupied + 1)
            } else if half_occupied > 0 {
                count_denied_recursive(groups, rest_start, a_remaining, b_remaining, half_occupied - 1)
            } else {
                1 + count_denied_recursive(groups, rest_start, a_remaining, b_remaining, half_occupied)
            }
        }
    }
}
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
    count_denied_recursive(&groups, 0, a, b, 0)
}
// </vc-code>


}

fn main() {}