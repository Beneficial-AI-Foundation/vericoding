// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): bounds cast from usize to int, avoid chained comparison */
proof fn lemma_usize_index_in_bounds(a: Vec<f32>, i: usize)
    requires i < a.len()
    ensures 0 <= i as int && i as int < a.len() as int
{ 
    assert(0 <= i as int);
    assert(i as int < a.len() as int);
}

/* helper modified by LLM (iteration 5): relate exec usize index with spec int index */
proof fn lemma_index_usize_int_eq(a: Vec<f32>, i: usize)
    requires i < a.len()
    ensures a[i as usize] == a[i as int]
{ 
    lemma_usize_index_in_bounds(a, i);
    assert(a[i as usize] == a[i as int]);
}

/* helper modified by LLM (iteration 5): extend nonzero prefix by one element */
proof fn lemma_extend_nonzero_prefix(a: Vec<f32>, i: int)
    requires
        0 <= i < a.len() as int,
        forall|j: int| 0 <= j < i ==> a[j] != 0.0f32,
        a[i] != 0.0f32
    ensures
        forall|j: int| 0 <= j < i + 1 ==> a[j] != 0.0f32
{
    assert forall|j: int| 0 <= j < i + 1 implies a[j] != 0.0f32 by {
        if j < i {
            assert(a[j] != 0.0f32);
        } else {
            assert(j >= i);
            assert(j < i + 1);
            assert(j == i);
            assert(a[j] != 0.0f32);
        }
    }
}
// </vc-helpers>

// <vc-spec>
fn all(a: Vec<f32>) -> (result: bool)
    ensures
        result == (forall|i: int| 0 <= i < a.len() ==> a[i] != 0.0f32),
        (a.len() == 0 ==> result == true),
        ((exists|i: int| 0 <= i < a.len() && a[i] == 0.0f32) ==> result == false),
        ((forall|i: int| 0 <= i < a.len() ==> a[i] != 0.0f32) ==> result == true),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): iterate with invariant over nonzero prefix and finalize forall proof */
    let mut i: usize = 0;
    while i < a.len()
        invariant
            i <= a.len(),
            forall|j: int| 0 <= j < i as int ==> a[j] != 0.0f32
        decreases (a.len() as int) - (i as int)
    {
        if a[i as usize] == 0.0f32 {
            proof {
                let ii: int = i as int;
                lemma_usize_index_in_bounds(a, i);
                lemma_index_usize_int_eq(a, i);
                assert(a[ii] == a[i as usize]);
                assert(a[ii] == 0.0f32);
                assert(exists|k: int| 0 <= k < a.len() as int && a[k] == 0.0f32) by {
                    assert(0 <= ii && ii < a.len() as int && a[ii] == 0.0f32);
                }
                assert(!(forall|k: int| 0 <= k < a.len() as int ==> a[k] != 0.0f32));
            }
            return false;
        } else {
            proof {
                let ii: int = i as int;
                lemma_usize_index_in_bounds(a, i);
                lemma_index_usize_int_eq(a, i);
                assert(a[ii] == a[i as usize]);
                assert(a[ii] != 0.0f32);
                lemma_extend_nonzero_prefix(a, ii);
            }
        }
        i = i + 1;
    }
    proof {
        assert(i <= a.len());
        assert(!(i < a.len()));
        assert(i == a.len());
        assert forall|j: int| 0 <= j < a.len() as int implies a[j] != 0.0f32 by {
            assert(0 <= j);
            assert(j < a.len() as int);
            assert(j < i as int);
        }
    }
    true
}
// </vc-code>

}
fn main() {}