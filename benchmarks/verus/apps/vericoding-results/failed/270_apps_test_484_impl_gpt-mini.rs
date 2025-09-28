// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn check_pair_func(seal1: (int, int), seal2: (int, int), a: int, b: int) -> int
{
    let orientations = seq![(seal1, seal2), (seal1, (seal2.1, seal2.0)), ((seal1.1, seal1.0), seal2), ((seal1.1, seal1.0), (seal2.1, seal2.0))];

    let area0 = if can_fit(orientations[0].0, orientations[0].1, a, b) {
        orientations[0].0.0 * orientations[0].0.1 + orientations[0].1.0 * orientations[0].1.1
    } else {
        0
    };

    let area1 = if can_fit(orientations[1].0, orientations[1].1, a, b) {
        orientations[1].0.0 * orientations[1].0.1 + orientations[1].1.0 * orientations[1].1.1
    } else {
        0
    };

    let area2 = if can_fit(orientations[2].0, orientations[2].1, a, b) {
        orientations[2].0.0 * orientations[2].0.1 + orientations[2].1.0 * orientations[2].1.1
    } else {
        0
    };

    let area3 = if can_fit(orientations[3].0, orientations[3].1, a, b) {
        orientations[3].0.0 * orientations[3].0.1 + orientations[3].1.0 * orientations[3].1.1
    } else {
        0
    };

    max_spec(max_spec(area0, area1), max_spec(area2, area3))
}

spec fn can_fit(r1: (int, int), r2: (int, int), a: int, b: int) -> bool
{
    (r1.0 + r2.0 <= a && max_spec(r1.1, r2.1) <= b) || (max_spec(r1.0, r2.0) <= a && r1.1 + r2.1 <= b)
}

spec fn max_spec(x: int, y: int) -> int
{
    if x >= y { x } else { y }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): check_pair_i8 bridges i8 inputs to int spec */
spec fn check_pair_i8(s1: (i8, i8), s2: (i8, i8), a: i8, b: i8) -> i8
{
    check_pair_func((s1.0 as int, s1.1 as int), (s2.0 as int, s2.1 as int), a as int, b as int) as i8
}

/* helper modified by LLM (iteration 5): max for i8 values */
spec fn max_i8(x: i8, y: i8) -> i8
{
    if x >= y { x } else { y }
}
// </vc-helpers>

// <vc-spec>
fn solve(n: i8, a: i8, b: i8, seals: Vec<(i8, i8)>) -> (result: i8)
    requires n >= 0,
            a >= 1 && b >= 1,
            seals.len() == n as nat,
            forall|i: int| 0 <= i < n as int ==> seals@[i].0 as int >= 1 && seals@[i].1 as int >= 1,
    ensures result as int >= 0,
            result as int == 0 ==> (forall|i: int, j: int| 0 <= i < n as int && i < j < n as int ==> check_pair_func((seals@[i].0 as int, seals@[i].1 as int), (seals@[j].0 as int, seals@[j].1 as int), a as int, b as int) == 0),
            result as int > 0 ==> (exists|i: int, j: int| 0 <= i < n as int && i < j < n as int && check_pair_func((seals@[i].0 as int, seals@[i].1 as int), (seals@[j].0 as int, seals@[j].1 as int), a as int, b as int) == result as int),
            forall|i: int, j: int| 0 <= i < n as int && i < j < n as int ==> check_pair_func((seals@[i].0 as int, seals@[i].1 as int), (seals@[j].0 as int, seals@[j].1 as int), a as int, b as int) <= result as int,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): iterate pairs using check_pair_i8 and keep res as i8 */
    let mut res: i8 = 0;
    let mut i: i8 = 0;
    while i < n
        invariant
            0 <= i as int && i as int <= n as int,
            forall|ii: int, jj: int| 0 <= ii < i as int && ii < jj < n as int ==> check_pair_i8(seals@[ii], seals@[jj], a, b) <= res,
        decreases n as int - i as int
    {
        let mut j: i8 = i + 1;
        while j < n
            invariant
                0 <= i as int && i as int <= n as int,
                0 <= j as int && j as int <= n as int,
                forall|ii: int, jj: int| 0 <= ii < i as int && ii < jj < n as int ==> check_pair_i8(seals@[ii], seals@[jj], a, b) <= res,
                forall|jj: int| i as int <= jj < j as int ==> check_pair_i8(seals@[i as int], seals@[jj], a, b) <= res,
            decreases n as int - j as int
        {
            let pair_area: i8 = check_pair_i8(seals[i as usize], seals[j as usize], a, b);
            if pair_area > res {
                res = pair_area;
            }
            j = j + 1;
        }
        i = i + 1;
    }
    res
}
// </vc-code>


}

fn main() {}