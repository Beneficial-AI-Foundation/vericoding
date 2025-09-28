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
    /* code modified by LLM (iteration 5): [brief description] */
    let mut max_area: i8 = 0;
    let n_local_nat = n as nat;

    if n_local_nat < 2 {
        return 0;
    }

    let mut i: nat = 0;
    while i < n_local_nat
        invariant
            0 <= i <= n_local_nat,
            max_area as int >= 0,
            forall|p: nat, q: nat|
                0 <= p < i && p < q < n_local_nat
                ==>
                check_pair_func((seals@p).0 as int, (seals@p).1 as int,
                                (seals@q).0 as int, (seals@q).1 as int,
                                a as int, b as int) <= max_area as int,
    {
        let mut j: nat = i + 1;
        while j < n_local_nat
            invariant
                0 <= i < j <= n_local_nat,
                max_area as int >= 0,
                forall|p: nat, q: nat|
                    (0 <= p < i && p < q < n_local_nat) || (p == i && i < q < j)
                    ==>
                    check_pair_func((seals@p).0 as int, (seals@p).1 as int,
                                    (seals@q).0 as int, (seals@q).1 as int,
                                    a as int, b as int) <= max_area as int,
        {
            let current_area_int = check_pair_func((seals@i).0 as int, (seals@i).1 as int,
                                                     (seals@j).0 as int, (seals@j).1 as int,
                                                     a as int, b as int);

            if current_area_int > max_area as int {
                max_area = current_area_int as i8;
            }
            j = j + 1_nat;
        }
        i = i + 1_nat;
    }
    max_area
}
// </vc-code>


}

fn main() {}