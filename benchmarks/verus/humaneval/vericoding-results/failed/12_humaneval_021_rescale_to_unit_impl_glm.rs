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
/* helper modified by LLM (iteration 5): fixed return type to anonymous tuple */
fn find_min_max(s: Vec<i8>) -> (i8, i8)
    requires
        s@.len() >= 2,
        exists|i: int, j: int| (0 <= i < j < s@.len()) && s@[i] != s@[j]
    ensures
        ret.0 as int <= ret.1 as int,
        forall|i: int| 0 <= i < s@.len() ==> ret.0 as int <= s@[i] as int && s@[i] as int <= ret.1 as int,
        exists|i: int| 0 <= i < s@.len() && s@[i] == ret.0,
        exists|i: int| 0 <= i < s@.len() && s@[i] == ret.1
{
    let mut min_val = s[0];
    let mut max_val = s[0];
    let mut i = 1;
    
    while i < s.len()
        invariant
            1 <= i <= s@.len(),
            forall|j: int| 0 <= j < i as int ==> min_val as int <= s@[j] as int && s@[j] as int <= max_val as int,
            exists|j: int| 0 <= j < i as int && s@[j] == min_val,
            exists|j: int| 0 <= j < i as int && s@[j] == max_val,
        decreases s@.len() - i as int
    {
        if s[i] < min_val {
            min_val = s[i];
        } else if s[i] > max_val {
            max_val = s[i];
        }
        i += 1;
    }
    
    (min_val, max_val)
}
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
/* code modified by LLM (iteration 5): updated to use fixed helper function */
{
    let (min_val, max_val) = find_min_max(s);
    let ghost shift_ghost = -(min_val as int);
    let ghost scale_ghost = (max_val as int) - (min_val as int);
    let shift = -(min_val as i32);
    let scale = (max_val as i32) - (min_val as i32);
    
    let mut r = Vec::new();
    let mut i = 0;
    
    while i < s.len()
        invariant
            0 <= i <= s@.len(),
            r@.len() == i,
            forall|j: int| 0 <= j < i as int ==> 
                r@[j] as int == affine(s@[j] as int, shift_ghost, scale_ghost),
        decreases s@.len() - i as int
    {
        let x = s[i] as i32;
        let scaled = (x + shift) / scale;
        r.push(scaled as i8);
        i += 1;
    }
    
    r
}
// </vc-code>


}

fn main() {}