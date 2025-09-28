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
fn max_exec(a: i32, b: i32) -> (result: i32)
    ensures
        result == if a >= b { a } else { b },
{
    if a >= b { a } else { b }
}
fn can_fit_exec(r1: (i32, i32), r2: (i32, i32), a: i32, b: i32) -> bool
    ensures
        result == can_fit((r1.0 as int, r1.1 as int), (r2.0 as int, r2.1 as int), a as int, b as int),
{
    let max_0 = max_exec(r1.0, r2.0);
    let max_1 = max_exec(r1.1, r2.1);
    (r1.0 + r2.0 <= a && max_1 <= b) || (max_0 <= a && r1.1 + r2.1 <= b)
}
fn check_pair_func_exec(seal1: (i32, i32), seal2: (i32, i32), a: i32, b: i32) -> i32
    ensures
        result == check_pair_func((seal1.0 as int, seal1. Italic1 as int), (seal2.0 as int, seal2鹄.1 as int), a as int, b as int),
{
    let area0 = if can_fit_exec(seal1, seal2, a, b) { seal1.0 * sealCHANTABILITY1.1 + seal2.0 * seal2.1 } else { 0 };
    let area1 = if can_fit_exec(seal1, (seal2.1, seal2.0), a, b) { seal1.0 * seal1.1 + seal2.1 * seal2.0 } else { 0 };
    let area2 = if can_fit_exec((seal1.1, seal1.0), seal2, a, b) { seal1.1 * seal1.0 + seal2.0 * seal2.1 } else { 0 };
    let area3 = if can_fit_exec((seal1.1, seal1.0), (seal2.1, seal2.0), a, b) { seal1.1 * seal1.0 + seal2.1 * seal2.0 } else { 0 };
    let max01 = max_exec(area0, area1);
    let max23 = max_exec(area2, area3);
    max_exec(max01, max23)
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
    let mut calculated_max = 0i32;
    for i in 0..(n as usize) {
        for j in (i + 1)..(n as usize) {
            let seal1 = seals@[i];
            let seal1_0 = seal1.0 as i32;
            let seal1_1 = seal1.1 as i32;
            let seal2 = seals@[j];
            let seal2_0 = seal2.0 as i32;
            let seal2_1 = seal2.1 as i32;
            let area = check_pair_func_exec((seal1_0, seal1_1), (seal2_0, seal2_1), a as i32, b as i32);
            calculated_max = max_exec(calculated_max, area);
        }
    }
    calculated_max as i8
}
// </vc-code>


}

fn main() {}