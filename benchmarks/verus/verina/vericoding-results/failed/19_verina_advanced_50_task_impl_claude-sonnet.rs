// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn is_sorted(v: Seq<nat>) -> bool {
    forall|i: int, j: int| 0 <= i < j < v.len() ==> #[trigger] v[i] <= #[trigger] v[j]
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed multiset import and lemmas */
use vstd::multiset::Multiset;

proof fn lemma_sorted_push(v: Seq<nat>, x: nat)
    requires is_sorted(v), v.len() == 0 || v[v.len() - 1] <= x
    ensures is_sorted(v.push(x))
{
    if v.len() > 0 {
        assert forall|i: int, j: int| 0 <= i < j < v.push(x).len() implies v.push(x)[i] <= v.push(x)[j] by {
            if j < v.len() {
                assert(v.push(x)[i] == v[i]);
                assert(v.push(x)[j] == v[j]);
            } else {
                assert(j == v.len());
                assert(v.push(x)[j] == x);
                if i < v.len() {
                    assert(v.push(x)[i] == v[i]);
                    assert(v[i] <= v[v.len() - 1]);
                    assert(v[v.len() - 1] <= x);
                } else {
                    assert(i == v.len());
                }
            }
        }
    }
}

proof fn lemma_subrange_multiset(v: Seq<nat>, i: int, j: int, x: nat)
    requires 0 <= i <= j <= v.len()
    ensures v.subrange(0, i).push(x).to_multiset() == v.subrange(0, i).to_multiset().insert(x)
{
    let sub = v.subrange(0, i);
    let pushed = sub.push(x);
    assert(pushed.to_multiset() =~= sub.to_multiset().insert(x));
}

proof fn lemma_merge_invariant_init(a1: Seq<nat>, a2: Seq<nat>)
    ensures a1.subrange(0, 0).to_multiset().add(a2.subrange(0, 0).to_multiset()) == Multiset::empty()
{
    assert(a1.subrange(0, 0) =~= Seq::empty());
    assert(a2.subrange(0, 0) =~= Seq::empty());
}

proof fn lemma_sorted_element_bound(v: Seq<nat>, result: Seq<nat>, idx: int)
    requires is_sorted(v), is_sorted(result), 0 <= idx < v.len(), result.len() > 0
    ensures result[result.len() - 1] <= v[idx] || v[idx] >= result[result.len() - 1]
{
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
    /* code modified by LLM (iteration 5): fixed invariant initialization and strengthened proofs */
    let mut result = Vec::new();
    let mut i = 0;
    let mut j = 0;
    
    proof {
        lemma_merge_invariant_init(a1@, a2@);
    }
    
    while i < a1.len() || j < a2.len()
        invariant
            i <= a1.len(),
            j <= a2.len(),
            is_sorted(result@),
            result@.to_multiset() == a1@.subrange(0, i as int).to_multiset().add(a2@.subrange(0, j as int).to_multiset()),
        decreases a1.len() + a2.len() - i - j
    {
        if i >= a1.len() {
            proof {
                if result@.len() > 0 {
                    let prev_multiset = result@.to_multiset();
                    let a1_part = a1@.subrange(0, i as int).to_multiset();
                    let a2_part = a2@.subrange(0, j as int).to_multiset();
                    let next_a2_part = a2@.subrange(0, (j + 1) as int).to_multiset();
                    
                    assert(next_a2_part == a2_part.insert(a2@[j as int]));
                }
                lemma_sorted_push(result@, a2@[j as int]);
            }
            result.push(a2[j]);
            j += 1;
        } else if j >= a2.len() {
            proof {
                if result@.len() > 0 {
                    let prev_multiset = result@.to_multiset();
                    let a1_part = a1@.subrange(0, i as int).to_multiset();
                    let a2_part = a2@.subrange(0, j as int).to_multiset();
                    let next_a1_part = a1@.subrange(0, (i + 1) as int).to_multiset();
                    
                    assert(next_a1_part == a1_part.insert(a1@[i as int]));
                }
                lemma_sorted_push(result@, a1@[i as int]);
            }
            result.push(a1[i]);
            i += 1;
        } else if a1[i] <= a2[j] {
            proof {
                lemma_sorted_push(result@, a1@[i as int]);
            }
            result.push(a1[i]);
            i += 1;
        } else {
            proof {
                lemma_sorted_push(result@, a2@[j as int]);
            }
            result.push(a2[j]);
            j += 1;
        }
    }
    
    proof {
        assert(i == a1.len() && j == a2.len());
        assert(a1@.subrange(0, i as int) =~= a1@);
        assert(a2@.subrange(0, j as int) =~= a2@);
    }
    
    result
}
// </vc-code>

}
fn main() {}