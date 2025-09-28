// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn is_sorted(v: Seq<nat>) -> bool {
    forall|i: int, j: int| 0 <= i < j < v.len() ==> #[trigger] v[i] <= #[trigger] v[j]
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fixed lemma parameters and simplified logic */
proof fn lemma_sorted_merge_step(result: Seq<nat>, a1: Seq<nat>, a2: Seq<nat>, i1: nat, i2: nat, next_val: nat)
    requires
        is_sorted(a1),
        is_sorted(a2),
        is_sorted(result),
        i1 <= a1.len(),
        i2 <= a2.len(),
        result == a1.subrange(0, i1 as int) + a2.subrange(0, i2 as int),
        (i1 < a1.len() && next_val == a1[i1 as int]) || (i2 < a2.len() && next_val == a2[i2 as int]),
        forall|k: int| 0 <= k < result.len() ==> result[k] <= next_val,
    ensures
        is_sorted(result.push(next_val)),
{
    assert forall|j: int, k: int| 0 <= j < k < result.push(next_val).len() implies result.push(next_val)[j] <= result.push(next_val)[k] by {
        if k < result.len() {
            assert(result.push(next_val)[j] == result[j]);
            assert(result.push(next_val)[k] == result[k]);
        } else {
            assert(k == result.len());
            assert(result.push(next_val)[k] == next_val);
            if j < result.len() {
                assert(result.push(next_val)[j] == result[j]);
            }
        }
    }
}
// </vc-helpers>

// <vc-spec>
fn merge_sorted(a1: &Vec<nat>, a2: &Vec<nat>) -> (result: Vec<nat>)
    requires 
        is_sorted(a1@),
        is_sorted(a2@),
    ensures
        is_sorted(result@),
        result@.to_multiset() == a1@.to_multiset().add(a2@.to_multiset()),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed type annotation for empty sequence */
    let mut result: Vec<nat> = Vec::new();
    let mut i1: usize = 0;
    let mut i2: usize = 0;
    
    proof {
        assert(result@ == seq![] as Seq<nat>);
        assert(a1@.subrange(0, 0) == seq![] as Seq<nat>);
        assert(a2@.subrange(0, 0) == seq![] as Seq<nat>);
        assert(result@ == a1@.subrange(0, 0) + a2@.subrange(0, 0));
        assert(is_sorted(result@));
    }
    
    while i1 < a1.len() || i2 < a2.len()
        invariant
            i1 <= a1.len(),
            i2 <= a2.len(),
            result@ == a1@.subrange(0, i1 as int) + a2@.subrange(0, i2 as int),
            is_sorted(result@),
            (i1 < a1.len() && i2 < a2.len()) ==> (
                forall|k: int| 0 <= k < i1 ==> a1@[k] <= a1@[i1 as int]
            ) && (
                forall|k: int| 0 <= k < i2 ==> a2@[k] <= a2@[i2 as int]
            ),
        decreases (a1.len() - i1) + (a2.len() - i2)
    {
        if i1 >= a1.len() {
            proof {
                assert(i2 < a2.len());
                assert forall|k: int| 0 <= k < result@.len() implies result@[k] <= a2@[i2 as int] by {
                    if k < i1 {
                        assert(result@[k] == a1@[k]);
                        assert(a1@[k] <= a1@[a1@.len() - 1]);
                        if i2 > 0 {
                            assert(a1@[a1@.len() - 1] <= a2@[i2 - 1]);
                            assert(a2@[i2 - 1] <= a2@[i2 as int]);
                        }
                    } else {
                        assert(result@[k] == a2@[k - i1]);
                        assert(a2@[k - i1] <= a2@[i2 as int]);
                    }
                }
                lemma_sorted_merge_step(result@, a1@, a2@, i1 as nat, i2 as nat, a2@[i2 as int]);
            }
            result.push(a2[i2]);
            i2 = i2 + 1;
        } else if i2 >= a2.len() {
            proof {
                assert(i1 < a1.len());
                assert forall|k: int| 0 <= k < result@.len() implies result@[k] <= a1@[i1 as int] by {
                    if k < i1 {
                        assert(result@[k] == a1@[k]);
                        assert(a1@[k] <= a1@[i1 as int]);
                    } else {
                        assert(result@[k] == a2@[k - i1]);
                        assert(a2@[k - i1] <= a2@[a2@.len() - 1]);
                        if i1 > 0 {
                            assert(a2@[a2@.len() - 1] <= a1@[i1 as int]);
                        }
                    }
                }
                lemma_sorted_merge_step(result@, a1@, a2@, i1 as nat, i2 as nat, a1@[i1 as int]);
            }
            result.push(a1[i1]);
            i1 = i1 + 1;
        } else {
            if a1[i1] <= a2[i2] {
                proof {
                    assert forall|k: int| 0 <= k < result@.len() implies result@[k] <= a1@[i1 as int] by {
                        if k < i1 {
                            assert(result@[k] == a1@[k]);
                            assert(a1@[k] <= a1@[i1 as int]);
                        } else {
                            assert(result@[k] == a2@[k - i1]);
                            if k - i1 < i2 {
                                assert(a2@[k - i1] <= a2@[i2 as int]);
                                assert(a2@[i2 as int] <= a1@[i1 as int] || a1@[i1 as int] <= a2@[i2 as int]);
                            }
                        }
                    }
                    lemma_sorted_merge_step(result@, a1@, a2@, i1 as nat, i2 as nat, a1@[i1 as int]);
                }
                result.push(a1[i1]);
                i1 = i1 + 1;
            } else {
                proof {
                    assert forall|k: int| 0 <= k < result@.len() implies result@[k] <= a2@[i2 as int] by {
                        if k < i1 {
                            assert(result@[k] == a1@[k]);
                            if k < i1 {
                                assert(a1@[k] <= a1@[i1 as int]);
                                assert(a1@[i1 as int] <= a2@[i2 as int] || a2@[i2 as int] < a1@[i1 as int]);
                            }
                        } else {
                            assert(result@[k] == a2@[k - i1]);
                            assert(a2@[k - i1] <= a2@[i2 as int]);
                        }
                    }
                    lemma_sorted_merge_step(result@, a1@, a2@, i1 as nat, i2 as nat, a2@[i2 as int]);
                }
                result.push(a2[i2]);
                i2 = i2 + 1;
            }
        }
    }
    
    proof {
        assert(i1 == a1.len());
        assert(i2 == a2.len());
        assert(a1@.subrange(0, a1.len() as int) == a1@);
        assert(a2@.subrange(0, a2.len() as int) == a2@);
        assert(result@.to_multiset() == a1@.subrange(0, i1 as int).to_multiset().add(a2@.subrange(0, i2 as int).to_multiset()));
        assert(result@.to_multiset() == a1@.to_multiset().add(a2@.to_multiset()));
    }
    
    result
}
// </vc-code>

}
fn main() {}