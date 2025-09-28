// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): added spec helpers and a proved lemma relating all_zero and has_nonzero */
pub open spec fn has_nonzero(s: Seq<f32>) -> bool {
    exists|i: int| 0 <= i && i < s.len() && s[i] != 0.0f32
}

/* helper modified by LLM (iteration 2): added spec helpers and a proved lemma relating all_zero and has_nonzero */
pub open spec fn all_zero(s: Seq<f32>) -> bool {
    forall|i: int| 0 <= i && i < s.len() ==> s[i] == 0.0f32
}

/* helper modified by LLM (iteration 2): proved that if all elements are zero, then there is no nonzero element */
pub proof fn zeros_imply_not_has_nonzero(s: Seq<f32>)
    ensures
        all_zero(s) ==> !has_nonzero(s),
{
    if all_zero(s) && has_nonzero(s) {
        let k = choose|k: int| 0 <= k && k < s.len() && s[k] != 0.0f32;
        assert(0 <= k && k < s.len());
        assert(s[k] != 0.0f32);
        // From all_zero(s) we have s[i] == 0 for all in range; in particular for k
        assert(s[k] == 0.0f32);
        assert(false);
    }
}

// </vc-helpers>

// <vc-spec>
fn any(v: Vec<f32>) -> (result: bool)
    ensures 
        (result == true <==> exists|i: int| 0 <= i < v@.len() && v@[i] != 0.0f32) &&
        (result == false <==> forall|i: int| 0 <= i < v@.len() ==> v@[i] == 0.0f32) &&
        (v@.len() == 0 ==> result == false) &&
        (forall|i: int| 0 <= i < v@.len() ==> v@[i] == 0.0f32 ==> result == false) &&
        (exists|i: int| 0 <= i < v@.len() && v@[i] != 0.0f32 ==> result == true) &&
        (result == true || result == false) &&
        !(result == true && result == false)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): implemented scan with invariant and fixed casts/parentheses in specs */
{
    let n = v.len();
    let mut i: usize = 0;
    let mut res: bool = false;

    while i < n
        invariant
            i <= n,
            res == (exists|j: int| 0 <= j && j < (i as int) && v@[j] != 0.0f32),
        decreases n - i
    {
        let idx = i;
        let prev_res = res;
        let is_nz = v[i] != 0.0f32;
        if is_nz {
            res = true;
        }
        i += 1;
        proof {
            assert(idx < n);
            assert(0 <= (idx as int));
            assert((idx as int) < (i as int));
            assert(v@[(idx as int)] == v[idx]);
            if prev_res {
                assert(exists|j: int| 0 <= j && j < (idx as int) && v@[j] != 0.0f32);
                assert(exists|j: int| 0 <= j && j < (i as int) && v@[j] != 0.0f32);
            } else {
                if is_nz {
                    assert(v@[(idx as int)] != 0.0f32);
                    assert(exists|j: int| 0 <= j && j < (i as int) && v@[j] != 0.0f32);
                } else {
                    assert(v@[(idx as int)] == 0.0f32);
                    assert(!(exists|j: int| 0 <= j && j < (idx as int) && v@[j] != 0.0f32));
                    assert(!(exists|j: int| 0 <= j && j < (i as int) && v@[j] != 0.0f32));
                }
            }
        }
    }
    proof {
        assert(i == n);
        assert((i as int) == v@.len());
    }
    result = res
}

// </vc-code>

}
fn main() {}