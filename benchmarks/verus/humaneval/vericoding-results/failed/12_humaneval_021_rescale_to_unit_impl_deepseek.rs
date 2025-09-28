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
/* helper modified by LLM (iteration 5): Fixed to use proper exec types instead of ghost types */
fn min_val_se(s: Seq<i8>) -> (result: i8)
    requires s.len() >= 2,
             exists|i: int, j: int| (0 <= i < j < s.len()) && s[i] != s[j]
    ensures exists|i: int| 0 <= i < s.len() && s[i] == result
{
    let mut min: i8 = s[0];
    let mut i: usize = 1;
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            forall|k: int| 0 <= k < i ==> min <= s[k],
            exists|k: int| 0 <= k < i && s[k] == min
        decreases s.len() - i
    {
        if s[i] < min {
            min = s[i];
        }
        i = i + 1;
    }
    min
}

fn max_val_se(s: Seq<i8>) -> (result: i8)
    requires s.len() >= 2,
             exists|i: int, j: int| (0 <= i < j < s.len()) && s[i] != s[j]
    ensures exists|i: int| 0 <= i < s.len() && s[i] == result
{
    let mut max: i8 = s[0];
    let mut i: usize = 1;
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            forall|k: int| 0 <= k < i ==> s[k] <= max,
            exists|k: int| 0 <= k < i && s[k] == max
        decreases s.len() - i
    {
        if s[i] > max {
            max = s[i];
        }
        i = i + 1;
    }
    max
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
/* code modified by LLM (iteration 5): Fixed int to i8 conversion and ghost code usage */
{
    let min_val: i8 = min_val_se(s@);
    let max_val: i8 = max_val_se(s@);
    let scale_int: int = (max_val as int) - (min_val as int);
    let shift_int: int = -(min_val as int);
    
    proof {
        assert(scale_int > 0) by {
            assert(exists|i: int, j: int| (0 <= i < j < s@.len()) && s@[i] != s@[j]);
            assert(min_val <= max_val);
            assert(max_val != min_val);
        };
    }
    
    let mut result = Vec::new();
    let mut i: usize = 0;
    
    while i < s.len()
        invariant
            i <= s@.len(),
            result@.len() == i,
            forall|k: int| 0 <= k < i ==> 0 <= result@[k] as int && result@[k] as int <= 1
        decreases s@.len() - i
    {
        let x_val: i8 = s[i];
        let normalized: i8 = (((x_val as int) + shift_int) / scale_int) as i8;
        result.push(normalized);
        i = i + 1;
    }
    
    result
}
// </vc-code>


}

fn main() {}