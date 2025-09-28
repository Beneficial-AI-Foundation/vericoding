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
    let gseq = groups@.map_values(|x: i8| x as int);
    let a_orig = a as int;
    let b_orig = b as int;
    let mut denied: int = 0;
    let mut aa: int = a_orig;
    let mut bb: int = b_orig;
    let mut half: int = 0;
    let mut i: usize = 0;
    while i < groups.len()
        invariant
            denied + count_denied_people_with_half(gseq.subrange(i as int, gseq.len() as int), aa, bb, half) == count_denied_people(gseq, a_orig, b_orig),
            aa >= 0,
            bb >= 0,
            half >= 0,
            i <= groups.len()
   
    {
        let group = gseq[i as int];
        if group == 2 {
            if bb > 0 {
                bb = bb - 1;
            } else {
                denied = denied + 2;
            }
        } else {
            if aa > 0 {
                aa = aa - 1;
            } else if bb > 0 {
                bb = bb - 1;
                half = half + 1;
            } else if half > 0 {
                half = half - 1;
            } else {
                denied = denied + 1;
            }
        }
        i = i + 1;
    }
    denied as i8
}
// </vc-code>


}

fn main() {}