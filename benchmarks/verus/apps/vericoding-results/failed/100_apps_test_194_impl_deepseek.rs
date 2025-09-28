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

proof fn lemma_count_denied_people_nonnegative(groups: Seq<int>, a: int, b: int, half_occupied: int) 
    ensures 
        count_denied_people_with_half(groups, a, b, half_occupied) >= 0
    decreases groups.len()
{
    if groups.len() == 0 {
    } else {
        let group = groups[0];
        let rest = groups.subrange(1, groups.len() as int);
        if group == 2 {
            if b > 0 {
                lemma_count_denied_people_nonnegative(rest, a, b - 1, half_occupied);
            } else {
                lemma_count_denied_people_nonnegative(rest, a, b, half_occupied);
            }
        } else {
            if a > 0 {
                lemma_count_denied_people_nonnegative(rest, a - 1, b, half_occupied);
            } else if b > 0 {
                lemma_count_denied_people_nonnegative(rest, a, b - 1, half_occupied + 1);
            } else if half_occupied > 0 {
                lemma_count_denied_people_nonnegative(rest, a, b, half_occupied - 1);
            } else {
                lemma_count_denied_people_nonnegative(rest, a, b, half_occupied);
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
    /* code modified by LLM (iteration 3): Fix is_empty() method usage, use len() instead */
    let mut denied = 0;
    let mut a_remaining = a;
    let mut b_remaining = b;
    let mut half_available = 0;
    
    for i in 0..groups.len() {
        let group = groups[i];
        if group == 2 {
            if b_remaining > 0 {
                b_remaining -= 1;
            } else {
                denied += 2;
            }
        } else {
            if a_remaining > 0 {
                a_remaining -= 1;
            } else if b_remaining > 0 {
                b_remaining -= 1;
                half_available += 1;
            } else if half_available > 0 {
                half_available -= 1;
            } else {
                denied += 1;
            }
        }
    }
    
    proof {
        lemma_count_denied_people_nonnegative(groups@.map_values(|x: i8| x as int), a as int, b as int, 0);
    }
    assert(denied >= 0);
    denied
}
// </vc-code>


}

fn main() {}