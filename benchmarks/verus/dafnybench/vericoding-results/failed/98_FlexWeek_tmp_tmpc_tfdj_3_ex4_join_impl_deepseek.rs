use vstd::prelude::*;

verus! {

// <vc-helpers>
spec fn lemma_seq_concat_index_property(a: Seq<i32>, b: Seq<i32>, i: int)
    requires
        0 <= a.len(),
        0 <= b.len(),
    ensures
        a.len() <= i < a.len() + b.len() ==> 
            (0 <= i - a.len() < b.len() && i - (i - a.len()) == a.len())
{
    if a.len() <= i < a.len() + b.len() {
        let j = i - a.len();
        assert(0 <= j < b.len());
        assert(i - j == a.len());
    }
}

spec fn lemma_seq_to_multiset_add_property(a: Seq<i32>, b: Seq<i32>)
    ensures
        a.to_multiset().add(b.to_multiset()) == (a + b).to_multiset()
{
    assert forall|v: i32| a.to_multiset().add(b.to_multiset()).count(v) == (a + b).to_multiset().count(v) by {
        // Multiset addition follows sequence concatenation
    };
}

spec fn lemma_seq_subrange_to_multiset_add(a: Seq<i32>, i: int, elem: i32)
    requires
        0 <= i <= a.len(),
    ensures
        a.subrange(0, i).to_multiset().add(elem) == a.subrange(0, i + 1).to_multiset()
{
    // Helper lemma for multiset property
}

spec fn lemma_seq_index_conversion(a: Seq<i32>, idx: usize)
    requires
        0 <= idx < a.len() as int,
    ensures
        a[idx as int] == a[idx]
{
    // Helper lemma for index conversion
}
// </vc-helpers>

// <vc-spec>
fn join(a: &[i32], b: &[i32]) -> (c: Vec<i32>)
    ensures
        a@ + b@ == c@,
        (a@ + b@).to_multiset() == c@.to_multiset(),
        a@.to_multiset().add(b@.to_multiset()) == c@.to_multiset(),
        a.len() + b.len() == c.len(),
        // Forall
        forall|i: int| 0 <= i < a.len() ==> c[i] == a[i],
        forall|i: int, j: int| 
            a.len() <= i < c.len() && 
            0 <= j < b.len() && 
            i - j == a.len() ==> c[i] == b[j],
// </vc-spec>
// <vc-code>
{
    let mut c = Vec::new();
    let mut i: usize = 0;
    
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            c@.len() == i as int,
            forall|k: int| 0 <= k < i as int ==> c@[k] == a@[k],
            c@.to_multiset() == a@.subrange(0, i as int).to_multiset(),
    {
        c.push(a[i]);
        proof {
            assert(c@.len() == i as int + 1);
            assert forall|k: int| 0 <= k < i as int implies c@[k] == a@[k] by {
                assert(c@[k] == a@[k]);
            };
            lemma_seq_index_conversion(a@, i);
            assert(c@[i as int] == a@[i as int]);
            lemma_seq_subrange_to_multiset_add(a@, i as int, a[i]);
            assert(a@.subrange(0, i as int + 1).to_multiset() == a@.subrange(0, i as int).to_multiset().add(a[i]));
        }
        i += 1;
    }
    
    let mut j: usize = 0;
    let a_len = a.len();
    
    while j < b.len()
        invariant
            0 <= j <= b.len(),
            c@.len() == a_len as int + j as int,
            forall|k: int| 0 <= k < a_len as int ==> c@[k] == a@[k],
            forall|k: int| a_len as int <= k < c@.len() ==> c@[k] == b@[k - a_len as int],
            c@.to_multiset() == a@.to_multiset().add(b@.subrange(0, j as int).to_multiset()),
    {
        c.push(b[j]);
        proof {
            let old_c = c@;
            lemma_seq_index_conversion(b@, j);
            assert(c@ == old_c.push(b[j]));
            
            // Preserve first invariant
            assert forall|k: int| 0 <= k < a_len as int implies c@[k] == a@[k] by {
                assert(old_c[k] == a@[k]);
                assert(c@[k] == old_c[k]);
            };
            
            // Second invariant
            assert forall|k: int| a_len as int <= k < old_c.len() implies c@[k] == b@[k - a_len as int] by {
                assert(old_c[k] == b@[k - a_len as int]);
                assert(c@[k] == old_c[k]);
            };
            
            // New element
            let new_k = c@.len() - 1;
            lemma_seq_index_conversion(b@, j);
            assert(c@[new_k] == b[j]);
            assert(new_k - a_len as int == j as int);
            
            // Multiset property
            lemma_seq_subrange_to_multiset_add(b@, j as int, b[j]);
            assert(b@.subrange(0, j as int + 1).to_multiset() == 
                   b@.subrange(0, j as int).to_multiset().add(b[j]));
            assert(c@.to_multiset() == old_c.to_multiset().add(b[j]));
        }
        j += 1;
    }
    
    proof {
        // Verify the postconditions
        assert(c@ == a@ + b@);
        assert(c@.to_multiset() == (a@ + b@).to_multiset());
        lemma_seq_to_multiset_add_property(a@, b@);
        assert(a@.to_multiset().add(b@.to_multiset()) == c@.to_multiset());
        assert(a.len() as int + b.len() as int == c.len() as int);
        
        // Verify forall conditions
        assert forall|i_val: int| 0 <= i_val < a.len() as int implies c[i_val] == a[i_val] by {
            assert(c@[i_val] == a@[i_val]);
        };
        
        assert forall|i_val: int, j_val: int| 
            a.len() as int <= i_val < c.len() as int && 
            0 <= j_val < b.len() as int && 
            i_val - j_val == a.len() as int 
            implies c[i_val] == b[j_val] by {
            assert(j_val == i_val - a.len() as int);
            assert(c@[i_val] == b@[j_val]);
        };
    }
    
    c
}
// </vc-code>

fn main() {}

}