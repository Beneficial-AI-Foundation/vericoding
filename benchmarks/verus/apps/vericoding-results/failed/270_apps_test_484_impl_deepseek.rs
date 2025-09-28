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
/* helper modified by LLM (iteration 5): Remove int casts and use spec functions directly */
spec fn max_spec_concrete(x: i8, y: i8) -> i8 {
    if x >= y { x } else { y }
}

spec fn can_fit_concrete(r1: (i8, i8), r2: (i8, i8), a: i8, b: i8) -> bool
{
    (r1.0 + r2.0 <= a && max_spec_concrete(r1.1, r2.1) <= b) || 
    (max_spec_concrete(r1.0, r2.0) <= a && r1.1 + r2.1 <= b)
}

spec fn check_pair_func_concrete(seal1: (i8, i8), seal2: (i8, i8), a: i8, b: i8) -> i8
{
    let orientations = seq![(seal1, seal2), (seal1, (seal2.1, seal2.0)), ((seal1.1, seal1.0), seal2), ((seal1.1, seal1.0), (seal2.1, seal2.0))];

    let area0 = if can_fit_concrete(orientations[0].0, orientations[0].1, a, b) {
        orientations[0].0.0 * orientations[0].0.1 + orientations[0].1.0 * orientations[0].1.1
    } else {
        0
    };

    let area1 = if can_fit_concrete(orientations[1].0, orientations[1].1, a, b) {
        orientations[1].0.0 * orientations[1].0.1 + orientations[1].1.0 * orientations[1].1.1
    } else {
        0
    };

    let area2 = if can_fit_concrete(orientations[2].0, orientations[2].1, a, b) {
        orientations[2].0.0 * orientations[2].0.1 + orientations[2].1.0 * orientations[2].1.1
    } else {
        0
    };

    let area3 = if can_fit_concrete(orientations[3].0, orientations[3].1, a, b) {
        orientations[3].0.0 * orientations[3].0.1 + orientations[3].1.0 * orientations[3].1.1
    } else {
        0
    };

    max_spec_concrete(max_spec_concrete(area0, area1), max_spec_concrete(area2, area3))
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
    /* code modified by LLM (iteration 5): Use proper ghost calls for verification */
    let mut result: i8 = 0;
    let mut i: usize = 0;
    
    proof {
        assert forall|k: int, l: int| 0 <= k < n as int && k < l < n as int implies check_pair_func((seals@[k].0 as int, seals@[k].1 as int), (seals@[l].0 as int, seals@[l].1 as int), a as int, b as int) >= 0 by {};
    }
    
    while i < n as usize
        invariant 0 <= i <= n as int,
                result as int >= 0,
                forall|k: int, l: int| 0 <= k < i && k < l < n as int ==> check_pair_func((seals@[k].0 as int, seals@[k].1 as int), (seals@[l].0 as int, seals@[l].1 as int), a as int, b as int) <= result as int,
                result == 0 ==> (forall|k: int, l: int| 0 <= k < i && k < l < n as int ==> check_pair_func((seals@[k].0 as int, seals@[k].1 as int), (seals@[l].0 as int, seals@[l].1 as int), a as int, b as int) == 0)
        decreases (n as int) - i
    {
        let mut j: usize = i + 1;
        while j < n as usize
            invariant i < j <= n as int,
                    result as int >= 0,
                    forall|l: int| i < l < j ==> check_pair_func((seals@[i].0 as int, seals@[i].1 as int), (seals@[l].0 as int, seals@[l].1 as int), a as int, b as int) <= result as int,
                    result == 0 ==> (forall|l: int| i < l < j ==> check_pair_func((seals@[i].0 as int, seals@[i].1 as int), (seals@[l].0 as int, seals@[l].1 as int), a as int, b as int) == 0)
            decreases (n as int) - j
        {
            let area_ghost = check_pair_func((seals@[i].0 as int, seals@[i].1 as int), (seals@[j].0 as int, seals@[j].1 as int), a as int, b as int);
            let area_concrete = check_pair_func_concrete(seals[i], seals[j], a, b);
            proof {
                assert area_ghost == area_concrete as int;
            }
            if area_concrete > 0 && area_concrete > result {
                result = area_concrete;
            }
            j = j + 1;
        }
        i = i + 1;
    }
    result
}
// </vc-code>


}

fn main() {}