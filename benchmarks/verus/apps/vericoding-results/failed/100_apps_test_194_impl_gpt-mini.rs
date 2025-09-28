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
/* helper modified by LLM (iteration 3): step_transition */
spec fn step_transition(groups: Seq<int>, a: int, b: int, half: int) -> (int, int, int, int)
    requires
        groups.len() > 0,
{
    let g = groups[0];
    if g == 2 {
        if b > 0 {
            (a, b - 1, half, 0)
        } else {
            (a, b, half, 2)
        }
    } else {
        if a > 0 {
            (a - 1, b, half, 0)
        } else if b > 0 {
            (a, b - 1, half + 1, 0)
        } else if half > 0 {
            (a, b, half - 1, 0)
        } else {
            (a, b, half, 1)
        }
    }
}

/* helper modified by LLM (iteration 3): proof that step_transition updates counts */
proof fn step_transition_correct(groups: Seq<int>, a: int, b: int, half: int)
    requires
        groups.len() > 0,
    ensures
        let tup = step_transition(groups, a, b, half);
        let rest = groups.subrange(1, groups.len() as int);
        count_denied_people_with_half(groups, a, b, half) == tup.3 + count_denied_people_with_half(rest, tup.0, tup.1, tup.2),
{
    proof {
        let g = groups[0];
        let rest = groups.subrange(1, groups.len() as int);
        let tup = step_transition(groups, a, b, half);
        if g == 2 {
            if b > 0 {
                assert(tup.0 == a);
                assert(tup.1 == b - 1);
                assert(tup.2 == half);
                assert(tup.3 == 0);
                assert(count_denied_people_with_half(groups, a, b, half) == count_denied_people_with_half(rest, a, b - 1, half));
            } else {
                assert(tup.0 == a);
                assert(tup.1 == b);
                assert(tup.2 == half);
                assert(tup.3 == 2);
                assert(count_denied_people_with_half(groups, a, b, half) == 2 + count_denied_people_with_half(rest, a, b, half));
            }
        } else {
            if a > 0 {
                assert(tup.0 == a - 1);
                assert(tup.1 == b);
                assert(tup.2 == half);
                assert(tup.3 == 0);
                assert(count_denied_people_with_half(groups, a, b, half) == count_denied_people_with_half(rest, a - 1, b, half));
            } else if b > 0 {
                assert(tup.0 == a);
                assert(tup.1 == b - 1);
                assert(tup.2 == half + 1);
                assert(tup.3 == 0);
                assert(count_denied_people_with_half(groups, a, b, half) == count_denied_people_with_half(rest, a, b - 1, half + 1));
            } else if half > 0 {
                assert(tup.0 == a);
                assert(tup.1 == b);
                assert(tup.2 == half - 1);
                assert(tup.3 == 0);
                assert(count_denied_people_with_half(groups, a, b, half) == count_denied_people_with_half(rest, a, b, half - 1));
            } else {
                assert(tup.0 == a);
                assert(tup.1 == b);
                assert(tup.2 == half);
                assert(tup.3 == 1);
                assert(count_denied_people_with_half(groups, a, b, half) == 1 + count_denied_people_with_half(rest, a, b, half));
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
    /* code modified by LLM (iteration 3): imperative simulation of groups using step_transition */
    let seq = groups@.map_values(|x: i8| x as int);
    let nn: int = n as int;
    let mut idx: int = 0;
    let mut ai: int = a as int;
    let mut bi: int = b as int;
    let mut half: int = 0;
    let mut den: int = 0;

    while idx < nn
        invariant
            0 <= idx,
            idx <= nn,
            den + count_denied_people_with_half(seq.subrange(idx, nn), ai, bi, half) == count_denied_people_with_half(seq, a as int, b as int, 0),
        decreases nn - idx
    {
        let prev_den = den;
        let old_ai = ai;
        let old_bi = bi;
        let old_half = half;

        let g = groups[idx as usize] as int;
        if g == 2 {
            if bi > 0 {
                bi = bi - 1;
            } else {
                den = den + 2;
            }
        } else {
            if ai > 0 {
                ai = ai - 1;
            } else if bi > 0 {
                bi = bi - 1;
                half = half + 1;
            } else if half > 0 {
                half = half - 1;
            } else {
                den = den + 1;
            }
        }

        proof {
            let rem = seq.subrange(idx, nn);
            step_transition_correct(rem, old_ai, old_bi, old_half);
            let tup = step_transition(rem, old_ai, old_bi, old_half);
            assert(tup.0 == ai);
            assert(tup.1 == bi);
            assert(tup.2 == half);
            assert(tup.3 == den - prev_den);
            let rest = seq.subrange(idx + 1, nn);
            assert(count_denied_people_with_half(rem, old_ai, old_bi, old_half) == tup.3 + count_denied_people_with_half(rest, tup.0, tup.1, tup.2));
        }

        idx = idx + 1;
    }

    (den as i8)
}

// </vc-code>


}

fn main() {}