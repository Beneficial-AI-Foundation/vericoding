// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
fn interpolate(x_val: i32, x1: i32, y1: i32, x2: i32, y2: i32) -> (result: i32)
    requires x1 < x2,
    ensures result == y1 + ((y2 - y1) as i64 * (x_val as i64 - x1 as i64) / (x2 as i64 - x1 as i64)) as i32,
{
    y1 + ((y2 - y1) as i64 * ((x_val - x1) as i64) / ((x2 - x1) as i64)) as i32
}
// </vc-helpers>

// <vc-spec>
fn interp(x: Vec<i32>, xp: Vec<i32>, fp: Vec<i32>) -> (result: Vec<i32>)
    requires 
        xp.len() > 0,
        fp.len() == xp.len(),
        x.len() > 0,
        forall|i: int, j: int| 0 <= i < j < xp.len() ==> xp[i] < xp[j],
    ensures 
        result.len() == x.len(),
        forall|k: int| 0 <= k < x.len() ==> (
            (x[k] <= xp[0] ==> result[k] == fp[0]) &&
            (x[k] >= xp[xp.len() - 1] ==> result[k] == fp[fp.len() - 1])
        )
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): fixed compilation errors by using .index() for Seq<T> indexing */
{
    let mut result = Vec::new();
    for k in 0..x.len() {
        let x_seq = x@;
        let xp_seq = xp@;
        let fp_seq = fp@;
        let mut i = 0;
        while i < (xp.len() - 1) && xp_seq.index((i + 1) as nat) <= x_seq.index(k as nat)
            invariant 0 <= i <= xp.len() - 1,
            decreases (xp.len() - 1 - i) as nat
        {
            i += 1;
        }
        let idx = i;
        if idx == 0 && x_seq.index(k as nat) <= xp_seq.index(0 as nat) {
            result.push(fp_seq.index(0 as nat));
        } else if idx == (xp.len() - 1) && x_seq.index(k as nat) >= xp_seq.index((xp.len() - 1) as nat) {
            result.push(fp_seq.index((xp.len() - 1) as nat));
        } else {
            let x1 = if idx == 0 { xp_seq.index(0 as nat) } else { xp_seq.index(idx as nat) };
            let y1 = if idx == 0 { fp_seq.index(0 as nat) } else { fp_seq.index(idx as nat) };
            let x2 = if idx == 0 { xp_seq.index(1 as nat) } else { xp_seq.index((idx + 1) as nat) };
            let y2 = if idx == 0 { fp_seq.index(1 as nat) } else { fp_seq.index((idx + 1) as nat) };
            let interp = interpolate(x_seq.index(k as nat), x1, y1, x2, y2);
            result.push(interp);
        }
    }
    result
}
// </vc-code>

}
fn main() {}