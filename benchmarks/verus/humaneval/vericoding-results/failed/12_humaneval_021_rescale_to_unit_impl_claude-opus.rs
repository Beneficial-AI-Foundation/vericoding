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
/* helper modified by LLM (iteration 5): Added explicit trigger annotations to forall assertion in proof */
proof fn lemma_affine_properties(s: Seq<int>, min_val: int, max_val: int)
    requires
        s.len() >= 2,
        min_val < max_val,
        forall|i: int| 0 <= i < s.len() ==> min_val <= #[trigger] s[i] <= max_val,
        exists|i: int| 0 <= i < s.len() && s[i] == min_val,
        exists|i: int| 0 <= i < s.len() && s[i] == max_val
    ensures
        forall|i: int| 0 <= i < s.len() ==> 0 <= #[trigger] affine(s[i], -min_val, max_val - min_val) <= 1,
        exists|i: int| 0 <= i < s.len() && affine(s[i], -min_val, max_val - min_val) == 0,
        exists|i: int| 0 <= i < s.len() && affine(s[i], -min_val, max_val - min_val) == 1
{
    assert(affine(min_val, -min_val, max_val - min_val) == 0);
    assert(affine(max_val, -min_val, max_val - min_val) == 1);
    assert forall|i: int| 0 <= i < s.len() implies 0 <= #[trigger] affine(s[i], -min_val, max_val - min_val) <= 1 by {
        let val = s[i];
        assert((val - min_val) / (max_val - min_val) >= 0);
        assert((val - min_val) / (max_val - min_val) <= 1);
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
    /* code modified by LLM (iteration 5): no changes needed */
    let mut min_val = s[0];
    let mut max_val = s[0];
    let mut i: usize = 1;
    
    while i < s.len()
        invariant
            1 <= i <= s.len(),
            forall|j: int| 0 <= j < i ==> min_val <= s@[j] <= max_val,
            exists|j: int| 0 <= j < i && s@[j] == min_val,
            exists|j: int| 0 <= j < i && s@[j] == max_val
        decreases s.len() - i
    {
        if s[i] < min_val {
            min_val = s[i];
        }
        if s[i] > max_val {
            max_val = s[i];
        }
        i = i + 1;
    }
    
    assert(min_val < max_val);
    let scale = (max_val - min_val) as i8;
    
    let mut result = Vec::new();
    let mut j: usize = 0;
    
    while j < s.len()
        invariant
            0 <= j <= s.len(),
            result@.len() == j,
            forall|k: int| 0 <= k < j ==> 0 <= result@[k] as int <= 1,
            forall|k: int| 0 <= k < j ==> result@[k] as int == affine(s@[k] as int, -(min_val as int), scale as int),
            scale > 0,
            min_val < max_val
        decreases s.len() - j
    {
        let val = ((s[j] - min_val) / scale) as i8;
        result.push(val);
        j = j + 1;
    }
    
    proof {
        let s_int = s@.map(|i, x| x as int);
        let r_int = result@.map(|i, x| x as int);
        lemma_affine_properties(s_int, min_val as int, max_val as int);
        assert(affine_seq(s_int, r_int, -(min_val as int), scale as int));
    }
    
    result
}
// </vc-code>


}

fn main() {}