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
fn vec_max(s: &Vec<i8>) -> (r: i8)
    requires
        s.len() >= 1,
    ensures
        exists|i: int| 0 <= i < s.len() && #[trigger] s[i] == r,
        forall|i: int| 0 <= i < s.len() ==> s[i] <= r,
{
    let mut max_val = s[0];
    let mut i: usize = 1;
    while i < s.len()
        invariant
            1 <= i <= s.len(),
            exists|j: int| 0 <= j < i && #[trigger] s[j] == max_val,
            forall|j: int| 0 <= j < i ==> s[j] <= max_val,
    {
        if s[i] > max_val {
            max_val = s[i];
        }
        i = i + 1;
    }
    max_val
}

fn vec_min(s: &Vec<i8>) -> (r: i8)
    requires
        s.len() >= 1,
    ensures
        exists|i: int| 0 <= i < s.len() && #[trigger] s[i] == r,
        forall|i: int| 0 <= i < s.len() ==> s[i] >= r,
{
    let mut min_val = s[0];
    let mut i: usize = 1;
    while i < s.len()
        invariant
            1 <= i <= s.len(),
            exists|j: int| 0 <= j < i && #[trigger] s[j] == min_val,
            forall|j: int| 0 <= j < i ==> s[j] >= min_val,
    {
        if s[i] < min_val {
            min_val = s[i];
        }
        i = i + 1;
    }
    min_val
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
    /* code modified by LLM (iteration 5): fixed incorrect arithmetic lemma names to pass compilation */
    let min_s = vec_min(&s);
    let max_s = vec_max(&s);

    proof {
        if min_s == max_s {
            let (i, j) = choose |i: int, j: int| 0 <= i < j < s@.len() && s@[i] != s@[j];
            assert(min_s <= s@[i] && s@[i] <= max_s);
            assert(min_s <= s@[j] && s@[j] <= max_s);
            assert(s@[i] == min_s);
            assert(s@[j] == max_s);
            assert(s@[i] == s@[j]);
            assert(false);
        }
    }
    assert(min_s < max_s);
    
    let min_val_exec = min_s as i32;
    let max_val_exec = max_s as i32;
    let scale_exec = max_val_exec - min_val_exec;
    let shift_exec = -min_val_exec;
    
    let ghost min_val_ghost = min_s as int;
    let ghost max_val_ghost = max_s as int;
    let ghost scale_ghost = max_val_ghost - min_val_ghost;
    let ghost shift_ghost = -min_val_ghost;
    
    proof {
        assert(scale_exec > 0);
        assert(scale_ghost > 0);
        assert forall|k: int| 0 <= k < s@.len() implies min_val_ghost <= s@[k] as int && s@[k] as int <= max_val_ghost by {
            assert(min_s <= s@[k] && s@[k] <= max_s);
        }
    }

    let mut r: Vec<i8> = Vec::new();
    let mut i: usize = 0;
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            r.len() == i,
            scale_ghost > 0,
            forall|j: int| 0 <= j < i ==> r@[j] as int == affine(s@[j] as int, shift_ghost, scale_ghost),
            forall|k: int| 0 <= k < s@.len() ==> min_val_ghost <= s@[k] as int && s@[k] as int <= max_val_ghost,
    {
        let s_i_val_exec = s[i] as i32;
        let r_i_int_exec = (s_i_val_exec + shift_exec) / scale_exec;

        proof {
            let s_i_val_ghost = s[i] as int;
            let r_val_spec = affine(s_i_val_ghost, shift_ghost, scale_ghost);
            let num_ghost = s_i_val_ghost - min_val_ghost;
            assert(0 <= num_ghost && num_ghost <= scale_ghost);
            if num_ghost < scale_ghost {
                vstd::arithmetic::div_mod::lemma_div_when_less(num_ghost, scale_ghost);
                assert(r_val_spec == 0);
            } else {
                assert(num_ghost == scale_ghost);
                vstd::arithmetic::div_mod::lemma_div_by_self(scale_ghost);
                assert(r_val_spec == 1);
            }
            assert(r_i_int_exec as int == r_val_spec);
        }
        
        let r_i = r_i_int_exec as i8;
        r.push(r_i);
        i += 1;
    }

    proof {
        let s_int = s@.map(|_idx, val| val as int);
        let r_int = r@.map(|_idx, val| val as int);
        assert(affine_seq(s_int, r_int, shift_ghost, scale_ghost));

        let k_min = choose |k: int| 0 <= k < s@.len() && s@[k] == min_s;
        let r_k_min_val = affine(s@[k_min] as int, shift_ghost, scale_ghost);
        let num_min = (s@[k_min] as int) - min_val_ghost;
        assert(num_min == 0);
        vstd::arithmetic::div_mod::lemma_div_when_less(num_min, scale_ghost);
        assert(r_k_min_val == 0);
        assert(r@[k_min] as int == 0);

        let k_max = choose |k: int| 0 <= k < s@.len() && s@[k] == max_s;
        let r_k_max_val = affine(s@[k_max] as int, shift_ghost, scale_ghost);
        let num_max = (s@[k_max] as int) - min_val_ghost;
        assert(num_max == scale_ghost);
        vstd::arithmetic::div_mod::lemma_div_by_self(scale_ghost);
        assert(r_k_max_val == 1);
        assert(r@[k_max] as int == 1);
    }

    r
}
// </vc-code>


}

fn main() {}