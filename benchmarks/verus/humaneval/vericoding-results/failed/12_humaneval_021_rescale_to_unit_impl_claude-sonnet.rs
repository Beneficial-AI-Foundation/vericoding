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
/* helper modified by LLM (iteration 5): fixed type annotations in assertions */
fn min_max_exist(s: Vec<i8>)
    requires s@.len() >= 2,
             exists|i: int, j: int| (0 <= i < j < s@.len()) && s@[i] != s@[j]
    ensures exists|min_val: int, max_val: int|
        min_val < max_val &&
        (exists|i: int| 0 <= i < s@.len() && s@[i] as int == min_val) &&
        (exists|i: int| 0 <= i < s@.len() && s@[i] as int == max_val) &&
        (forall|i: int| 0 <= i < s@.len() ==> min_val <= s@[i] as int <= max_val)
{
    proof {
        let min_val = s@[0] as int;
        let max_val = s@[0] as int;
        assert(exists|min_val: int, max_val: int| 
            min_val <= max_val &&
            (exists|i: int| 0 <= i < s@.len() && s@[i] as int == min_val) &&
            (exists|i: int| 0 <= i < s@.len() && s@[i] as int == max_val) &&
            (forall|i: int| 0 <= i < s@.len() ==> min_val <= s@[i] as int <= max_val));
    }
}

fn affine_properties(s_int: Seq<int>, min_val: int, max_val: int, shift: int, scale: int)
    requires min_val < max_val,
             shift == -min_val,
             scale == max_val - min_val,
             s_int.len() >= 1
    ensures scale > 0,
            affine(min_val, shift, scale) == 0,
            affine(max_val, shift, scale) == 1,
            forall|x: int| min_val <= x <= max_val ==> 0 <= affine(x, shift, scale) <= 1
{
    proof {
        assert(scale == max_val - min_val);
        assert(min_val < max_val);
        assert(scale > 0);
        assert(affine(min_val, shift, scale) == (min_val + shift) / scale);
        assert(affine(min_val, shift, scale) == (min_val + (-min_val)) / scale);
        assert(affine(min_val, shift, scale) == 0int / scale);
        assert(affine(min_val, shift, scale) == 0int);
        assert(affine(max_val, shift, scale) == (max_val + shift) / scale);
        assert(affine(max_val, shift, scale) == (max_val + (-min_val)) / scale);
        assert(affine(max_val, shift, scale) == (max_val - min_val) / scale);
        assert(affine(max_val, shift, scale) == scale / scale);
        assert(affine(max_val, shift, scale) == 1int);
    }
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
{
    /* code modified by LLM (iteration 5): fixed type annotations in proof and implementation */
    let mut min_val = s[0];
    let mut max_val = s[0];
    
    let mut i = 1;
    while i < s.len()
        invariant
            1 <= i <= s.len(),
            exists|j: int| 0 <= j < i && s@[j] == min_val,
            exists|j: int| 0 <= j < i && s@[j] == max_val,
            forall|j: int| 0 <= j < i ==> min_val <= s@[j] <= max_val
    {
        if s[i] < min_val {
            min_val = s[i];
        }
        if s[i] > max_val {
            max_val = s[i];
        }
        i += 1;
    }
    
    proof {
        min_max_exist(s);
        let ghost shift: int = -(min_val as int);
        let ghost scale: int = (max_val as int) - (min_val as int);
        affine_properties(s@.map(|i, x| x as int), min_val as int, max_val as int, shift, scale);
    }
    
    let mut result = Vec::new();
    let mut j = 0;
    
    while j < s.len()
        invariant
            0 <= j <= s.len(),
            result@.len() == j,
            forall|k: int| 0 <= k < j ==> result@[k] as int == affine(s@[k] as int, -(min_val as int), (max_val as int) - (min_val as int)),
            (max_val as int) - (min_val as int) > 0
    {
        let transformed = ((s[j] - min_val) / (max_val - min_val)) as i8;
        result.push(transformed);
        j += 1;
    }
    
    result
}
// </vc-code>


}

fn main() {}