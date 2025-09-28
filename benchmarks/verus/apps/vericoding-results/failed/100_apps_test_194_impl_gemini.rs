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
/* helper modified by LLM (iteration 4): Fixed compilation error by changing `#[verus::proof]` to `proof fn`. */
proof fn lemma_count_denied_unfold(groups: Seq<int>, a: int, b: int, half_occupied: int)
    requires
        groups.len() > 0,
    ensures
        count_denied_people_with_half(groups, a, b, half_occupied) ==
            if groups[0] == 2 {
                if b > 0 {
                    count_denied_people_with_half(groups.subrange(1, groups.len() as int), a, b - 1, half_occupied)
                } else {
                    2 + count_denied_people_with_half(groups.subrange(1, groups.len() as int), a, b, half_occupied)
                }
            } else {
                if a > 0 {
                    count_denied_people_with_half(groups.subrange(1, groups.len() as int), a - 1, b, half_occupied)
                } else if b > 0 {
                    count_denied_people_with_half(groups.subrange(1, groups.len() as int), a, b - 1, half_occupied + 1)
                } else if half_occupied > 0 {
                    count_denied_people_with_half(groups.subrange(1, groups.len() as int), a, b, half_occupied - 1)
                } else {
                    1 + count_denied_people_with_half(groups.subrange(1, groups.len() as int), a, b, half_occupied)
                }
            },
{
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
/* code modified by LLM (iteration 4): No changes made to the code; the fix is for a compilation error in a helper function. */
{
    let mut a_rem = a;
    let mut b_rem = b;
    let mut half_occupied: i8 = 0;
    let mut denied: i8 = 0;
    let mut i: i8 = 0;

    let ghost spec_groups = groups@.map_values(|x: i8| x as int);

    while i < n
        invariant
            0 <= i <= n,
            a_rem >= 0,
            b_rem >= 0,
            half_occupied >= 0,
            b_rem as int + half_occupied as int <= b as int,
            denied >= 0,
            spec_groups === groups@.map_values(|x: i8| x as int),
            valid_input(n as int, a as int, b as int, spec_groups),
            denied as int + count_denied_people_with_half(
                spec_groups.subrange(i as int, n as int),
                a_rem as int,
                b_rem as int,
                half_occupied as int
            ) == count_denied_people(spec_groups, a as int, b as int),
        decreases n - i
    {
        proof {
            lemma_count_denied_unfold(
                spec_groups.subrange(i as int, n as int),
                a_rem as int,
                b_rem as int,
                half_occupied as int
            );
        }

        let group = groups[i as usize];
        if group == 2 {
            if b_rem > 0 {
                b_rem = b_rem - 1;
            } else {
                denied = denied + 2;
            }
        } else {
            if a_rem > 0 {
                a_rem = a_rem - 1;
            } else if b_rem > 0 {
                b_rem = b_rem - 1;
                half_occupied = half_occupied + 1;
            } else if half_occupied > 0 {
                half_occupied = half_occupied - 1;
            } else {
                denied = denied + 1;
            }
        }
        i = i + 1;
    }

    denied
}

// </vc-code>


}

fn main() {}