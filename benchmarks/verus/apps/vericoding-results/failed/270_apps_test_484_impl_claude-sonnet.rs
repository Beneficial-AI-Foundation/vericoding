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
/* helper modified by LLM (iteration 5): fixed compilation error in can_fit_exec function */
fn max_exec(x: i8, y: i8) -> (result: i8)
    ensures result as int == max_spec(x as int, y as int)
{
    if x >= y { x } else { y }
}

fn can_fit_exec(r1: (i8, i8), r2: (i8, i8), a: i8, b: i8) -> (result: bool)
    requires
        r1.0 >= 0 && r1.1 >= 0 && r2.0 >= 0 && r2.1 >= 0,
        a >= 0 && b >= 0,
        r1.0 <= 100 && r1.1 <= 100 && r2.0 <= 100 && r2.1 <= 100,
    ensures
        result == can_fit((r1.0 as int, r1.1 as int), (r2.0 as int, r2.1 as int), a as int, b as int)
{
    if r1.0 > a - r2.0 && max_exec(r1.0, r2.0) > a {
        false
    } else if r1.1 > b - r2.1 && max_exec(r1.1, r2.1) > b {
        false  
    } else {
        (r1.0 <= a - r2.0 && max_exec(r1.1, r2.1) <= b) || (max_exec(r1.0, r2.0) <= a && r1.1 <= b - r2.1)
    }
}

fn check_pair_exec(seal1: (i8, i8), seal2: (i8, i8), a: i8, b: i8) -> (result: i8)
    requires
        seal1.0 >= 1 && seal1.1 >= 1 && seal2.0 >= 1 && seal2.1 >= 1,
        a >= 1 && b >= 1,
        seal1.0 <= 100 && seal1.1 <= 100 && seal2.0 <= 100 && seal2.1 <= 100,
    ensures
        result as int == check_pair_func((seal1.0 as int, seal1.1 as int), (seal2.0 as int, seal2.1 as int), a as int, b as int)
{
    let orientations = [(seal1, seal2), (seal1, (seal2.1, seal2.0)), ((seal1.1, seal1.0), seal2), ((seal1.1, seal1.0), (seal2.1, seal2.0))];
    
    let mut max_area = 0i8;
    
    let mut i = 0;
    while i < 4
        invariant
            0 <= i <= 4,
            max_area >= 0,
        decreases 4 - i
    {
        let (r1, r2) = orientations[i];
        if can_fit_exec(r1, r2, a, b) {
            if r1.0 <= 63 && r1.1 <= 63 && r2.0 <= 63 && r2.1 <= 63 {
                let area = r1.0 * r1.1 + r2.0 * r2.1;
                if area > max_area {
                    max_area = area;
                }
            }
        }
        i += 1;
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
    /* code modified by LLM (iteration 5): fixed compilation error by using proper bounds in proof assertion */
    if n <= 1 {
        return 0;
    }
    
    let mut max_result = 0i8;
    
    let mut i = 0;
    while i < n - 1
        invariant
            0 <= i <= n - 1,
            max_result >= 0,
            forall|k: int, l: int| 0 <= k < i as int && k < l < n as int ==> check_pair_func((seals@[k].0 as int, seals@[k].1 as int), (seals@[l].0 as int, seals@[l].1 as int), a as int, b as int) <= max_result as int,
        decreases n - 1 - i
    {
        let mut j = i + 1;
        while j < n
            invariant
                i + 1 <= j <= n,
                max_result >= 0,
                i < n as int,
                forall|k: int, l: int| 0 <= k < i as int && k < l < n as int ==> check_pair_func((seals@[k].0 as int, seals@[k].1 as int), (seals@[l].0 as int, seals@[l].1 as int), a as int, b as int) <= max_result as int,
                forall|l: int| i < l < j as int ==> check_pair_func((seals@[i].0 as int, seals@[i].1 as int), (seals@[l].0 as int, seals@[l].1 as int), a as int, b as int) <= max_result as int,
            decreases n - j
        {
            proof {
                assert(i < n as int);
                assert(j < n as int);
                assert(i as usize < seals@.len());
                assert(j as usize < seals@.len());
            }
            let result = check_pair_exec(seals[i as usize], seals[j as usize], a, b);
            if result > max_result {
                max_result = result;
            }
            j += 1;
        }
        i += 1;
    }
    
    max_result
}
// </vc-code>


}

fn main() {}