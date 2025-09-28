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
/* helper modified by LLM (iteration 4): safe i32 helpers with preconditions to avoid overflow */
fn max_i32(x: i32, y: i32) -> i32 {
    if x >= y { x } else { y }
}

fn can_fit_i32(r1: (i32, i32), r2: (i32, i32), a: i32, b: i32) -> bool
    requires
        0 <= r1.0, 0 <= r1.1, 0 <= r2.0, 0 <= r2.1,
        0 <= a, 0 <= b,
        r1.0 <= 127, r1.1 <= 127, r2.0 <= 127, r2.1 <= 127,
        a <= 127, b <= 127,
{
    let sum_w = r1.0 + r2.0;
    let sum_h = r1.1 + r2.1;
    (sum_w <= a && max_i32(r1.1, r2.1) <= b)
        || (max_i32(r1.0, r2.0) <= a && sum_h <= b)
}

fn check_pair_i32(r1: (i32, i32), r2: (i32, i32), a: i32, b: i32) -> i32
    requires
        0 <= r1.0, 0 <= r1.1, 0 <= r2.0, 0 <= r2.1,
        0 <= a, 0 <= b,
        r1.0 <= 127, r1.1 <= 127, r2.0 <= 127, r2.1 <= 127,
        a <= 127, b <= 127,
{
    let area0 = if can_fit_i32(r1, r2, a, b) { r1.0 * r1.1 + r2.0 * r2.1 } else { 0 };
    let area1 = if can_fit_i32(r1, (r2.1, r2.0), a, b) { r1.0 * r1.1 + r2.1 * r2.0 } else { 0 };
    let area2 = if can_fit_i32((r1.1, r1.0), r2, a, b) { r1.1 * r1.0 + r2.0 * r2.1 } else { 0 };
    let area3 = if can_fit_i32((r1.1, r1.0), (r2.1, r2.0), a, b) { r1.1 * r1.0 + r2.1 * r2.0 } else { 0 };
    max_i32(max_i32(area0, area1), max_i32(area2, area3))
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
    /* code modified by LLM (iteration 4): use bounded-ints helpers with asserts to satisfy preconditions and avoid overflow */
    let len = seals.len();
    let mut best: i32 = 0;
    let mut i: usize = 0;
    while i < len
        invariant
            seals.len() == len,
            i <= len,
            best >= 0,
        decreases len - i
    {
        let mut j: usize = i + 1;
        while j < len
            invariant
                seals.len() == len,
                i < len,
                i <= j,
                j <= len,
                best >= 0,
            decreases len - j
        {
            let (w1, h1) = seals[i];
            let (w2, h2) = seals[j];

            // establish helper preconditions (values are i8 so in [-128,127], and per requires >= 0)
            assert((w1 as i32) >= 0); assert((w1 as i32) <= 127);
            assert((h1 as i32) >= 0); assert((h1 as i32) <= 127);
            assert((w2 as i32) >= 0); assert((w2 as i32) <= 127);
            assert((h2 as i32) >= 0); assert((h2 as i32) <= 127);
            assert((a as i32) >= 0);  assert((a as i32) <= 127);
            assert((b as i32) >= 0);  assert((b as i32) <= 127);

            let area = check_pair_i32((w1 as i32, h1 as i32), (w2 as i32, h2 as i32), a as i32, b as i32);
            if area > best {
                best = area;
            }
            j += 1;
        }
        i += 1;
    }
    let mut res: i8 = 0;
    if best > 127 {
        res = 127;
    } else if best < 0 {
        res = 0;
    } else {
        res = best as i8;
    }
    res
}
// </vc-code>


}

fn main() {}