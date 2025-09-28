// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn affine(x: int, shift: int, scale: int) -> int {
    if scale > 0 { (x + shift) / scale } else { 0 }
}

spec fn affine_seq(s: Seq<int>, r: Seq<int>, shift: int, scale: int) -> bool {
    scale > 0 && r.len() == s.len() &&
    forall|i: int| 0 <= i < s.len() ==> #[trigger] r[i] == #[trigger] affine(s[i], shift, scale)
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn rescale_to_unit(s: Vec<i8>) -> (r: Vec<i8>)
    requires s@.len() >= 2,
             exists|i: int, j: int| (0 <= i < j < s@.len()) && s@[i] != s@[j]
    ensures r@.len() == s@.len(),
            forall|i: int| 0 <= i < s@.len() ==> 0 <= r@[i] as int && r@[i] as int <= 1,
            exists|i: int| 0 <= i < s@.len() && r@[i] as int == 0,
            exists|i: int| 0 <= i < s@.len() && r@[i] as int == 1,
            ({
                let s_int = s@.map(|i, x| x as int);
                let r_int = r@.map(|i, x| x as int);
                exists|shift: int, scale: int| affine_seq(s_int, r_int, shift, scale) && scale > 0
            })
// </vc-spec>
// <vc-code>
{
/* code modified by LLM (iteration 3): use i64 for computations to avoid using int in exec code */
    let mut min_i64: i64 = s[0] as i64;
    let mut max_i64: i64 = min_i64;
    let mut i: usize = 1;
    while i < s.len()
        invariant
            1 <= i <= s.len(),
            forall|j: int| 0 <= j < i ==> s@[j] as i64 >= min_i64,
            forall|j: int| 0 <= j < i ==> s@[j] as i64 <= max_i64,
        decreases s.len() - i
    {
        let val: i64 = s[i] as i64;
        if val < min_i64 {
            min_i64 = val;
        }
        if val > max_i64 {
            max_i64 = val;
        }
        i += 1;
    }
    let shift: i64 = -min_i64;
    let scale: i64 = max_i64 - min_i64;
    let mut r = Vec::new();
    i = 0;
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            r@.len() == i as int,
            forall|j: int| 0 <= j < i ==> {
                let val_j = s@[j] as i64;
                let res = (val_j + shift as int) / (scale as int);
                r@[j] as int == res && 0 <= res <= 1
            },
        decreases s.len() - i
    {
        let val: i64 = s[i] as i64;
        let res: i64 = (val + shift) / scale;
        r.push(res as i8);
        i += 1;
    }
    r
}
// </vc-code>


}

fn main() {}