// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): construct a 2-element Vec pair with proven contents */
fn make_pair(a: f32, b: f32) -> (result: Vec<f32>)
    ensures
        result@.len() == 2,
        result@[0] == a,
        result@[1] == b
{
    let mut v: Vec<f32> = Vec::new();
    v.push(a);
    v.push(b);
    v
}
// </vc-helpers>

// <vc-spec>
fn c_(arr1: Vec<f32>, arr2: Vec<f32>) -> (result: Vec<Vec<f32>>)
    requires arr1.len() == arr2.len(),
    ensures 
        result.len() == arr1.len(),
        forall|i: int| 0 <= i < result.len() ==> 
            result[i].len() == 2 &&
            result[i][0] == arr1[i] &&
            result[i][1] == arr2[i]
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): implement loop, use assert_forall_by with single ensures to maintain invariants */
    let n_usize: usize = arr1.len();
    let mut out: Vec<Vec<f32>> = Vec::new();
    let mut i: usize = 0;
    while i < n_usize
        invariant
            out.len() == i,
            forall|k: int| 0 <= k < i as int ==>
                out@[k]@.len() == 2 &&
                out@[k]@[0] == arr1@[k] &&
                out@[k]@[1] == arr2@[k]
        decreases (n_usize as int) - (i as int)
    {
        let a = arr1[i];
        let b = arr2[i];
        let p = make_pair(a, b);

        let ghost j: int = i as int;
        proof {
            assert(arr1@[j] == a);
            assert(arr2@[j] == b);
            assert(p@.len() == 2);
            assert(p@[0] == a);
            assert(p@[1] == b);
        }

        let ghost old_out = out@;
        proof {
            assert(old_out.len() == j);
            // Capture facts about old_out derived from loop invariant before mutation
            assert_forall_by(|k: int| {
                requires 0 <= k && k < j;
                ensures old_out[k]@.len() == 2 && old_out[k]@[0] == arr1@[k] && old_out[k]@[1] == arr2@[k];
                // From loop invariant at loop head (i == j)
                assert(0 <= k && k < j);
                assert(old_out == out@);
                assert(out@[k]@.len() == 2);
                assert(out@[k]@[0] == arr1@[k]);
                assert(out@[k]@[1] == arr2@[k]);
                // Rewrite via equality old_out == out@
                assert(old_out[k] == out@[k]);
            });
        }

        out.push(p);

        proof {
            assert(out@ == old_out.push(p));
            // Establish invariant for i + 1
            assert_forall_by(|k: int| {
                requires 0 <= k && k < j + 1;
                ensures out@[k]@.len() == 2 && out@[k]@[0] == arr1@[k] && out@[k]@[1] == arr2@[k];
                if k < j {
                    // For k < j, the element is unchanged by push
                    assert(out@ == old_out.push(p));
                    assert(k < old_out.len());
                    assert(out@[k] == (old_out.push(p))[k]);
                    assert((old_out.push(p))[k] == old_out[k]);
                    // Use captured facts about old_out
                    assert(old_out[k]@.len() == 2);
                    assert(old_out[k]@[0] == arr1@[k]);
                    assert(old_out[k]@[1] == arr2@[k]);
                } else {
                    // k == j is the newly pushed element
                    assert(k == j);
                    assert(old_out.len() == j);
                    assert(out@ == old_out.push(p));
                    assert(out@[j] == (old_out.push(p))[j]);
                    assert((old_out.push(p))[j] == p);
                    assert(out@[j]@.len() == 2);
                    assert(out@[j]@[0] == a);
                    assert(out@[j]@[1] == b);
                    assert(arr1@[j] == a);
                    assert(arr2@[j] == b);
                }
            });
        }

        i = i + 1;
    }
    out
}
// </vc-code>

}
fn main() {}