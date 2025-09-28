// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): refined prefix and existence lemmas for loop invariants */
proof fn lemma_forall_prefix_step(s: Seq<f32>, i: int)
    requires
        0 <= i < s.len(),
        forall|j:int| 0 <= j < i ==> s[j] != 0.0f32,
        s[i] != 0.0f32,
    ensures
        forall|j:int| 0 <= j < i + 1 ==> s[j] != 0.0f32,
{
    assert forall|j:int| 0 <= j < i + 1 ==> s[j] != 0.0f32 by {
        if 0 <= j && j < i + 1 {
            if j < i {
                assert(s[j] != 0.0f32);
            } else {
                assert(j >= i);
                assert(j < i + 1);
                assert(j == i);
                assert(s[j] != 0.0f32);
            }
        }
    };
}

/* helper modified by LLM (iteration 5): provide witness when current element is zero */
proof fn lemma_exists_zero_at_end(s: Seq<f32>, i: int)
    requires
        0 <= i < s.len(),
        s[i] == 0.0f32,
    ensures
        exists|j:int| 0 <= j < i + 1 && s[j] == 0.0f32,
{
    assert(exists|j:int| 0 <= j < i + 1 && s[j] == 0.0f32) by {
        let j = i;
    };
}

/* helper modified by LLM (iteration 5): extend existential from prefix of length i to i+1 */
proof fn lemma_exists_prefix_monotonic(s: Seq<f32>, i: int)
    requires
        exists|j:int| 0 <= j < i && s[j] == 0.0f32,
    ensures
        exists|j:int| 0 <= j < i + 1 && s[j] == 0.0f32,
{
    let j = choose|j:int| 0 <= j < i && s[j] == 0.0f32;
    assert(j < i + 1);
    assert(exists|k:int| 0 <= k < i + 1 && s[k] == 0.0f32) by {
        let k = j;
    };
}
// </vc-helpers>

// <vc-spec>
fn all(a: Vec<f32>) -> (result: bool)
    ensures
        result == (forall|i: int| 0 <= i < a@.len() ==> a@[i] != 0.0f32),
        (a@.len() == 0 ==> result == true),
        ((exists|i: int| 0 <= i < a@.len() && a@[i] == 0.0f32) ==> result == false),
        ((forall|i: int| 0 <= i < a@.len() ==> a@[i] != 0.0f32) ==> result == true),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): cleaned loop proofs and avoided problematic assert usage */
    let mut i: usize = 0;
    let mut res: bool = true;
    while i < a.len()
        invariant
            0 <= i as int,
            i as int <= a@.len(),
            res ==> (forall|j: int| 0 <= j < i as int ==> a@[j] != 0.0f32),
            !res ==> (exists|j: int| 0 <= j < i as int && a@[j] == 0.0f32),
        decreases a@.len() - i as int
    {
        let ai = a[i];
        if res {
            if ai == 0.0f32 {
                res = false;
                proof {
                    assert(a@.len() == a.len() as int);
                    assert(i < a.len());
                    assert(ai == a@[i as int]);
                    lemma_exists_zero_at_end(a@, i as int);
                }
            } else {
                proof {
                    assert(a@.len() == a.len() as int);
                    assert(i < a.len());
                    assert(i as int < a.len() as int);
                    assert(ai == a@[i as int]);
                    assert(a@[i as int] != 0.0f32);
                    lemma_forall_prefix_step(a@, i as int);
                }
            }
        } else {
            proof {
                assert(a@.len() == a.len() as int);
                assert(i < a.len());
                assert(i as int < a.len() as int);
                lemma_exists_prefix_monotonic(a@, i as int);
            }
        }
        i = i + 1;
    }
    proof {
        assert(i as int == a@.len());
        if res {
            assert(forall|j:int| 0 <= j < a@.len() ==> a@[j] != 0.0f32) by {
                assert forall|j:int| 0 <= j < a@.len() ==> a@[j] != 0.0f32 by {
                    if 0 <= j && j < a@.len() {
                        assert(0 <= j && j < i as int);
                    }
                }
            };
        } else {
            assert(exists|j:int| 0 <= j < a@.len() && a@[j] == 0.0f32) by {
                let j0 = choose|j:int| 0 <= j < i as int && a@[j] == 0.0f32;
                assert(0 <= j0 && j0 < a@.len());
            };
            assert(!(forall|j:int| 0 <= j < a@.len() ==> a@[j] != 0.0f32)) by {
                let w = choose|k:int| 0 <= k < a@.len() && a@[k] == 0.0f32;
                assert(0 <= w && w < a@.len());
                assert(!(a@[w] != 0.0f32));
            };
        }
    }
    res
}
// </vc-code>

}
fn main() {}