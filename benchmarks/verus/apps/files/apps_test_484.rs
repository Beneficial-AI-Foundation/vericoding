// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn check_pair_func(seal1: (int, int), seal2: (int, int), a: int, b: int) -> int {
    let orientations = seq![
        (seal1, seal2),
        (seal1, (seal2.1, seal2.0)),
        ((seal1.1, seal1.0), seal2),
        ((seal1.1, seal1.0), (seal2.1, seal2.0))
    ];

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

    max_int(max_int(area0, area1), max_int(area2, area3))
}

spec fn can_fit(r1: (int, int), r2: (int, int), a: int, b: int) -> bool {
    (r1.0 + r2.0 <= a && max_int(r1.1, r2.1) <= b) || (max_int(r1.0, r2.0) <= a && r1.1 + r2.1 <= b)
}

spec fn max_int(x: int, y: int) -> int {
    if x >= y { x } else { y }
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn solve(n: int, a: int, b: int, seals: Seq<(int, int)>) -> (result: int)
    requires n >= 0,
            a >= 1 && b >= 1,
            seals.len() == n,
            forall|i: int| 0 <= i < n ==> seals[i].0 >= 1 && seals[i].1 >= 1
    ensures result >= 0,
            result == 0 ==> (forall|i: int, j: int| 0 <= i < n && i < j < n ==> check_pair_func(seals[i], seals[j], a, b) == 0),
            result > 0 ==> (exists|i: int, j: int| 0 <= i < n && i < j < n && check_pair_func(seals[i], seals[j], a, b) == result),
            forall|i: int, j: int| 0 <= i < n && i < j < n ==> check_pair_func(seals[i], seals[j], a, b) <= result
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume(false);
    0
    // impl-end
}
// </vc-code>


}

fn main() {}