// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): trivial lemma about usize to int non-negativity */
proof fn lemma_usize_nonneg(u: usize)
    ensures
        0 <= u as int,
{
    assert(0 <= u as int);
}

// </vc-helpers>

// <vc-spec>
fn hermesub(c1: Vec<i8>, c2: Vec<i8>) -> (result: Vec<i8>)
    ensures
        result.len() == if c1.len() >= c2.len() { c1.len() } else { c2.len() },
        forall|i: int| 0 <= i < result@.len() ==> 
            #[trigger] result@[i] == 
            (if i < c1@.len() { c1@[i] } else { 0 }) - 
            (if i < c2@.len() { c2@[i] } else { 0 })
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): capture result@ as a ghost value (prev) and use push's view to maintain invariant */
    let m: usize = if c1.len() >= c2.len() { c1.len() } else { c2.len() };
    let mut result: Vec<i8> = Vec::new();
    let mut j: usize = 0;
    while j < m
        invariant
            result.len() == j,
            j <= m,
            forall|k: int| 0 <= k < j as int ==> #[trigger] result@[k] ==
                (if k < c1@.len() { c1@[k] } else { 0 }) -
                (if k < c2@.len() { c2@[k] } else { 0 }),
        decreases m as int - j as int
    {
        let ghost prev = result@;
        proof {
            let old_j: int = j as int;
            assert forall|k: int| 0 <= k < old_j implies
                prev[k] ==
                    (if k < c1@.len() { c1@[k] } else { 0 }) -
                    (if k < c2@.len() { c2@[k] } else { 0 }) by {
                if 0 <= k && k < old_j {
                    assert(result@[k] ==
                        (if k < c1@.len() { c1@[k] } else { 0 }) -
                        (if k < c2@.len() { c2@[k] } else { 0 }));
                    assert(prev[k] == result@[k]);
                }
            }
        }
        let x: i8 = if j < c1.len() { c1[j] } else { 0i8 };
        let y: i8 = if j < c2.len() { c2[j] } else { 0i8 };
        let z: i8 = x - y;
        result.push(z);
        proof {
            let old_j: int = j as int;
            let new_len: int = old_j + 1;
            assert(prev.len() == old_j);
            assert(result@ == prev.push(z));
            assert forall|k: int| 0 <= k < new_len implies
                #[trigger] result@[k] ==
                    (if k < c1@.len() { c1@[k] } else { 0 }) -
                    (if k < c2@.len() { c2@[k] } else { 0 }) by {
                if 0 <= k && k < new_len {
                    if k < old_j {
                        assert(result@[k] == prev[k]);
                        assert(prev[k] ==
                            (if k < c1@.len() { c1@[k] } else { 0 }) -
                            (if k < c2@.len() { c2@[k] } else { 0 }));
                    } else {
                        assert(k == old_j);
                        assert(result@[old_j] == z);
                        if j < c1.len() {
                            assert(old_j < c1@.len());
                            assert(x == c1@[old_j]);
                        } else {
                            assert(!(old_j < c1@.len()));
                        }
                        if j < c2.len() {
                            assert(old_j < c2@.len());
                            assert(y == c2@[old_j]);
                        } else {
                            assert(!(old_j < c2@.len()));
                        }
                        assert(z ==
                            (if old_j < c1@.len() { c1@[old_j] } else { 0 }) -
                            (if old_j < c2@.len() { c2@[old_j] } else { 0 }));
                    }
                }
            }
        }
        j = j + 1;
    }
    result
}

// </vc-code>


}
fn main() {}