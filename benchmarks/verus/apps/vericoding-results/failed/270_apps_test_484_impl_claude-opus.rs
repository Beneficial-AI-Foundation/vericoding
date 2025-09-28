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
/* helper modified by LLM (iteration 4): Added overflow prevention and fixed preconditions */
fn max(x: i8, y: i8) -> (result: i8)
    requires
        x >= 0,
        y >= 0,
        x <= 127,
        y <= 127,
    ensures
        result == if x >= y { x } else { y },
        result == max_spec(x as int, y as int),
{
    if x >= y { x } else { y }
}

fn can_fit_exec(r1: (i8, i8), r2: (i8, i8), a: i8, b: i8) -> (result: bool)
    requires
        r1.0 >= 1 && r1.1 >= 1,
        r2.0 >= 1 && r2.1 >= 1,
        a >= 1 && b >= 1,
        r1.0 <= 127 && r1.1 <= 127,
        r2.0 <= 127 && r2.1 <= 127,
        a <= 127 && b <= 127,
    ensures
        result == can_fit((r1.0 as int, r1.1 as int), (r2.0 as int, r2.1 as int), a as int, b as int),
{
    if r1.0 as int + r2.0 as int <= 127 && r1.1 as int + r2.1 as int <= 127 {
        (r1.0 + r2.0 <= a && max(r1.1, r2.1) <= b) || (max(r1.0, r2.0) <= a && r1.1 + r2.1 <= b)
    } else if r1.0 as int + r2.0 as int <= a as int {
        max(r1.1, r2.1) <= b
    } else if r1.1 as int + r2.1 as int <= b as int {
        max(r1.0, r2.0) <= a
    } else {
        false
    }
}

fn check_pair(seal1: (i8, i8), seal2: (i8, i8), a: i8, b: i8) -> (result: i8)
    requires
        seal1.0 >= 1 && seal1.1 >= 1,
        seal2.0 >= 1 && seal2.1 >= 1,
        a >= 1 && b >= 1,
        seal1.0 <= 64 && seal1.1 <= 64,
        seal2.0 <= 64 && seal2.1 <= 64,
        a <= 127 && b <= 127,
    ensures
        result as int == check_pair_func((seal1.0 as int, seal1.1 as int), (seal2.0 as int, seal2.1 as int), a as int, b as int),
        result >= 0,
{
    let mut max_area: i8 = 0;
    
    // Compute area once (it's the same for all orientations)
    let area = if seal1.0 as int * seal1.1 as int + seal2.0 as int * seal2.1 as int <= 127 {
        seal1.0 * seal1.1 + seal2.0 * seal2.1
    } else {
        127  // cap at max value
    };
    
    // Check all 4 orientations
    if can_fit_exec(seal1, seal2, a, b) {
        if area > max_area {
            max_area = area;
        }
    }
    
    if can_fit_exec(seal1, (seal2.1, seal2.0), a, b) {
        if area > max_area {
            max_area = area;
        }
    }
    
    if can_fit_exec((seal1.1, seal1.0), seal2, a, b) {
        if area > max_area {
            max_area = area;
        }
    }
    
    if can_fit_exec((seal1.1, seal1.0), (seal2.1, seal2.0), a, b) {
        if area > max_area {
            max_area = area;
        }
    }
    
    max_area
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
    /* code modified by LLM (iteration 4): Fixed loop invariants and tracked witnesses */
    let mut max_area: i8 = 0;
    let mut i: usize = 0;
    let mut witness_i: usize = 0;
    let mut witness_j: usize = 0;
    
    while i < n as usize
        invariant
            0 <= i <= n as nat,
            n >= 0,
            max_area >= 0,
            max_area <= 127,
            seals.len() == n as nat,
            forall|k: int| 0 <= k < n as int ==> seals@[k].0 >= 1 && seals@[k].1 >= 1,
            forall|k: int| 0 <= k < n as int ==> seals@[k].0 <= 64 && seals@[k].1 <= 64,
            forall|ii: int, jj: int| 0 <= ii < i as int && ii < jj < n as int ==> check_pair_func((seals@[ii].0 as int, seals@[ii].1 as int), (seals@[jj].0 as int, seals@[jj].1 as int), a as int, b as int) <= max_area as int,
            max_area > 0 ==> witness_i < witness_j && witness_j < n as nat && check_pair_func((seals@[witness_i as int].0 as int, seals@[witness_i as int].1 as int), (seals@[witness_j as int].0 as int, seals@[witness_j as int].1 as int), a as int, b as int) == max_area as int,
        decreases (n as int - i as int)
    {
        let mut j: usize = i + 1;
        while j < n as usize
            invariant
                i + 1 <= j <= n as nat,
                0 <= i < n as nat,
                n >= 0,
                max_area >= 0,
                max_area <= 127,
                seals.len() == n as nat,
                forall|k: int| 0 <= k < n as int ==> seals@[k].0 >= 1 && seals@[k].1 >= 1,
                forall|k: int| 0 <= k < n as int ==> seals@[k].0 <= 64 && seals@[k].1 <= 64,
                forall|ii: int, jj: int| 0 <= ii < i as int && ii < jj < n as int ==> check_pair_func((seals@[ii].0 as int, seals@[ii].1 as int), (seals@[jj].0 as int, seals@[jj].1 as int), a as int, b as int) <= max_area as int,
                forall|jj: int| i as int < jj < j as int ==> check_pair_func((seals@[i as int].0 as int, seals@[i as int].1 as int), (seals@[jj as int].0 as int, seals@[jj as int].1 as int), a as int, b as int) <= max_area as int,
                max_area > 0 ==> witness_i < witness_j && witness_j < n as nat && check_pair_func((seals@[witness_i as int].0 as int, seals@[witness_i as int].1 as int), (seals@[witness_j as int].0 as int, seals@[witness_j as int].1 as int), a as int, b as int) == max_area as int,
            decreases (n as int - j as int)
        {
            let area = check_pair(seals[i], seals[j], a, b);
            if area > max_area {
                max_area = area;
                witness_i = i;
                witness_j = j;
            }
            j = j + 1;
        }
        i = i + 1;
    }
    
    max_area
}
// </vc-code>


}

fn main() {}