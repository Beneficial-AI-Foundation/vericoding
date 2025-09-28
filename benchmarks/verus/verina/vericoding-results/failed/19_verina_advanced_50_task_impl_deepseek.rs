// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn is_sorted(v: Seq<nat>) -> bool {
    forall|i: int, j: int| 0 <= i < j < v.len() ==> #[trigger] v[i] <= #[trigger] v[j]
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fixed Seq type annotation and added Multiset proofs */
use vstd::multiset::Multiset;

proof fn lemma_seq_to_multiset_add_commutative(x: Seq<nat>, y: Seq<nat>) 
    ensures 
        x.to_multiset().add(y.to_multiset()) == y.to_multiset().add(x.to_multiset())
{
    assert(x.to_multiset().add(y.to_multiset()) =~= y.to_multiset().add(x.to_multiset()));
}

proof fn lemma_merge_sorted_preserves_multiset(a1: Seq<nat>, a2: Seq<nat>, result: Seq<nat>)
    requires
        is_sorted(a1),
        is_sorted(a2),
        is_sorted(result),
        result.to_multiset() == a1.to_multiset().add(a2.to_multiset())
    ensures
        result.to_multiset() == a2.to_multiset().add(a1.to_multiset())
{
    lemma_seq_to_multiset_add_commutative(a1, a2);
}

spec fn merge_sorted_spec(a1: Seq<nat>, a2: Seq<nat>) -> Seq<nat> 
    decreases a1.len() + a2.len()
{
    recommends(a1.len() + a2.len() <= 1000000000);
    if a1.len() == 0 {
        a2
    } else if a2.len() == 0 {
        a1
    } else if a1[0] <= a2[0] {
        let rest = merge_sorted_spec(a1.subrange(1, a1.len() as int), a2);
        Seq::new(1 + rest.len(), |i: int| if i == 0 { a1[0] } else { rest[i - 1] })
    } else {
        let rest = merge_sorted_spec(a1, a2.subrange(1, a2.len() as int));
        Seq::new(1 + rest.len(), |i: int| if i == 0 { a2[0] } else { rest[i - 1] })
    }
}

proof fn merge_sorted_spec_ensures_sorted(a1: Seq<nat>, a2: Seq<nat>)
    requires
        is_sorted(a1),
        is_sorted(a2)
    ensures
        is_sorted(merge_sorted_spec(a1, a2))
    decreases a1.len() + a2.len()
{
    if a1.len() > 0 && a2.len() > 0 {
        if a1[0] <= a2[0] {
            let sub_a1 = a1.subrange(1, a1.len() as int);
            merge_sorted_spec_ensures_sorted(sub_a1, a2);
        } else {
            let sub_a2 = a2.subrange(1, a2.len() as int);
            merge_sorted_spec_ensures_sorted(a1, sub_a2);
        }
    }
}

proof fn merge_sorted_spec_preserves_multiset(a1: Seq<nat>, a2: Seq<nat>)
    ensures
        merge_sorted_spec(a1, a2).to_multiset() == a1.to_multiset().add(a2.to_multiset())
    decreases a1.len() + a2.len()
{
    if a1.len() == 0 {
        // Base case: a1 empty
    } else if a2.len() == 0 {
        // Base case: a2 empty
    } else if a1[0] <= a2[0] {
        let sub_a1 = a1.subrange(1, a1.len() as int);
        merge_sorted_spec_preserves_multiset(sub_a1, a2);
    } else {
        let sub_a2 = a2.subrange(1, a2.len() as int);
        merge_sorted_spec_preserves_multiset(a1, sub_a2);
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
/* code modified by LLM (iteration 5): Fixed Seq type annotation in proof block */
{
    let mut result = Vec::new();
    let mut i = 0;
    let mut j = 0;
    
    proof {
        assert(is_sorted(Seq::<nat>::empty()));
        assert(Seq::<nat>::empty().to_multiset() == Multiset::empty());
    }
    
    while i < a1.len() && j < a2.len()
        invariant
            0 <= i <= a1.len(),
            0 <= j <= a2.len(),
            is_sorted(result@),
            result@.to_multiset() == a1@.subrange(0, i as int).to_multiset().add(a2@.subrange(0, j as int).to_multiset())
        decreases (a1.len() - i) + (a2.len() - j)
    {
        if a1[i] <= a2[j] {
            result.push(a1[i]);
            i += 1;
        } else {
            result.push(a2[j]);
            j += 1;
        }
    }
    
    while i < a1.len()
        invariant
            i <= a1.len(),
            j == a2.len(),
            is_sorted(result@),
            result@.to_multiset() == a1@.subrange(0, i as int).to_multiset().add(a2@.subrange(0, j as int).to_multiset())
        decreases a1.len() - i
    {
        result.push(a1[i]);
        i += 1;
    }
    
    while j < a2.len()
        invariant
            i == a1.len(),
            j <= a2.len(),
            is_sorted(result@),
            result@.to_multiset() == a1@.subrange(0, i as int).to_multiset().add(a2@.subrange(0, j as int).to_multiset())
        decreases a2.len() - j
    {
        result.push(a2[j]);
        j += 1;
    }
    
    proof {
        merge_sorted_spec_ensures_sorted(a1@, a2@);
        merge_sorted_spec_preserves_multiset(a1@, a2@);
        assert(result@.to_multiset() == a1@.to_multiset().add(a2@.to_multiset()));
    }
    
    result
}
// </vc-code>

}
fn main() {}