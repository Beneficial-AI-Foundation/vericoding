// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn is_sorted(s: Seq<i32>) -> bool {
    forall|i: int, j: int| 0 <= i < j < s.len() ==> s[i] <= s[j]
}

spec fn multiset_equiv(s1: Seq<i32>, s2: Seq<i32>) -> bool {
    s1.to_multiset() == s2.to_multiset()
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fixed lemma preconditions and added trigger annotations */

proof fn lemma_push_maintains_sorted(result: Seq<i32>, val: i32)
    requires
        is_sorted(result),
        forall|k: int| 0 <= k < result.len() ==> result[k] <= val,
    ensures
        is_sorted(result.push(val))
{
    let new_seq = result.push(val);
    assert forall|i: int, j: int| 0 <= i < j < new_seq.len() implies new_seq[i] <= new_seq[j] by {
        if j < result.len() {
            assert(new_seq[i] == result[i]);
            assert(new_seq[j] == result[j]);
        } else {
            assert(j == result.len());
            assert(new_seq[j] == val);
            if i < result.len() {
                assert(new_seq[i] == result[i]);
                assert(result[i] <= val);
            }
        }
    }
}

proof fn lemma_maintains_multiset(old_result: Seq<i32>, new_val: i32, old_a: Seq<i32>, old_b: Seq<i32>, new_a: Seq<i32>, new_b: Seq<i32>)
    requires
        old_result + old_a + old_b == old_a + old_b,
        new_a + new_b == old_a.drop_first() + old_b || new_a + new_b == old_a + old_b.drop_first(),
        (old_a.len() > 0 && new_val == old_a[0]) || (old_b.len() > 0 && new_val == old_b[0]),
    ensures
        old_result.push(new_val) + new_a + new_b == old_a + old_b
{
}
// </vc-helpers>

// <vc-spec>
fn merge_sorted(a: Vec<i32>, b: Vec<i32>) -> (result: Vec<i32>)
    requires 
        is_sorted(a@),
        is_sorted(b@),
    ensures 
        is_sorted(result@),
        multiset_equiv(result@, a@ + b@),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Added trigger annotations to fix quantifier inference */
    let mut result = Vec::new();
    let mut i = 0;
    let mut j = 0;
    
    while i < a.len() || j < b.len()
        invariant
            i <= a.len(),
            j <= b.len(),
            is_sorted(result@),
            multiset_equiv(result@ + a@.subrange(i as int, a.len() as int) + b@.subrange(j as int, b.len() as int), a@ + b@),
        decreases a.len() + b.len() - i - j
    {
        if i >= a.len() {
            proof {
                assert(j < b.len());
                assert(forall|k: int| #[trigger] result@[k] <= b[j as int] when 0 <= k < result@.len());
                if result@.len() > 0 {
                    lemma_push_maintains_sorted(result@, b[j as int]);
                }
            }
            result.push(b[j]);
            j += 1;
        } else if j >= b.len() {
            proof {
                assert(i < a.len());
                if result@.len() > 0 {
                    lemma_push_maintains_sorted(result@, a[i as int]);
                }
            }
            result.push(a[i]);
            i += 1;
        } else if a[i] <= b[j] {
            proof {
                if result@.len() > 0 {
                    lemma_push_maintains_sorted(result@, a[i as int]);
                }
            }
            result.push(a[i]);
            i += 1;
        } else {
            proof {
                if result@.len() > 0 {
                    lemma_push_maintains_sorted(result@, b[j as int]);
                }
            }
            result.push(b[j]);
            j += 1;
        }
    }
    
    result
}
// </vc-code>

}
fn main() {}