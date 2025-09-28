use vstd::prelude::*;

verus! {

spec fn strict_negative(v: &Vec<i32>, i: usize, j: usize) -> bool
    recommends 0 <= i <= j <= v.len()
{
    forall|u: usize| i <= u < j ==> v[u as int] < 0
}

spec fn positive(s: Seq<i32>) -> bool {
    forall|u: int| 0 <= u < s.len() ==> s[u] >= 0
}

spec fn is_permutation(s: Seq<i32>, t: Seq<i32>) -> bool {
    s.to_multiset() == t.to_multiset()
}

/**
returns an index st new array is a permutation of the old array
positive first and then strictnegative, i is the firs neg or len if not any */

// <vc-helpers>
proof fn lemma_swap_preserves_permutation(v: &Vec<i32>, old_v: Seq<i32>, i: usize, j: usize)
    requires 
        0 <= i < v.len(),
        0 <= j < v.len(),
        old_v.len() == v.len(),
        forall|k: int| #![auto] 0 <= k < v.len() && k != i && k != j ==> v[k as int] == old_v[k],
        v[i as int] == old_v[j as int],
        v[j as int] == old_v[i as int],
    ensures
        is_permutation(v@, old_v)
{
    assert(v@.to_multiset() =~= old_v.to_multiset());
}

proof fn lemma_subrange_positive_after_swap(v: &Vec<i32>, old_v: &Vec<i32>, swap_pos: usize, neg_pos: usize)
    requires
        0 <= swap_pos < neg_pos < v.len(),
        positive(old_v@.subrange(0, swap_pos as int)),
        old_v[neg_pos as int] >= 0,
        old_v[swap_pos as int] < 0,
        forall|k: int| 0 <= k < v.len() && k != swap_pos && k != neg_pos ==> v[k as int] == old_v[k as int],
        v[swap_pos as int] == old_v[neg_pos as int],
        v[neg_pos as int] == old_v[swap_pos as int],
    ensures
        positive(v@.subrange(0, (swap_pos + 1) as int))
{
    let subrange = v@.subrange(0, (swap_pos + 1) as int);
    assert(forall|idx: int| 0 <= idx < subrange.len() ==> subrange[idx] >= 0) by {
        assert(forall|idx: int| 0 <= idx < (swap_pos + 1) as int ==> {
            if idx == swap_pos as int {
                subrange[idx] == v[swap_pos as int] && v[swap_pos as int] == old_v[neg_pos as int] && old_v[neg_pos as int] >= 0
            } else {
                subrange[idx] == v[idx] && v[idx] == old_v[idx] && old_v@.subrange(0, swap_pos as int)[idx] >= 0
            }
        });
    }
}
// </vc-helpers>

// <vc-spec>
fn separate(v: &mut Vec<i32>) -> (i: usize)
    ensures
        0 <= i <= v.len(),
        positive(v@.subrange(0, i as int)),
        strict_negative(v, i, v.len()),
        is_permutation(v@, old(v)@),
// </vc-spec>
// <vc-code>
{
    let ghost original_v = v@;
    let mut i = 0;
    
    while i < v.len()
        invariant
            0 <= i <= v.len(),
            positive(v@.subrange(0, i as int)),
            is_permutation(v@, original_v),
    {
        if v[i] >= 0 {
            i = i + 1;
        } else {
            let mut j = i + 1;
            let mut found = false;
            
            while j < v.len() && !found
                invariant
                    i < j <= v.len(),
                    positive(v@.subrange(0, i as int)),
                    is_permutation(v@, original_v),
                    forall|k: usize| i < k < j ==> v[k as int] < 0,
                    found ==> (j < v.len() && v[j as int] >= 0),
                    !found ==> forall|k: usize| (i + 1) <= k < j ==> v[k as int] < 0,
                decreases v.len() - j
            {
                if v[j] >= 0 {
                    found = true;
                } else {
                    j = j + 1;
                }
            }
            
            if found {
                let ghost old_v_before_swap = v@;
                let temp = v[i];
                let temp_j = v[j];
                v.set(i, temp_j);
                v.set(j, temp);
                
                proof {
                    assert(old_v_before_swap.len() == v.len());
                    assert(forall|k: int| #![auto] 0 <= k < v.len() && k != i && k != j ==> v[k as int] == old_v_before_swap[k]);
                    assert(v[i as int] == old_v_before_swap[j as int]);
                    assert(v[j as int] == old_v_before_swap[i as int]);
                    
                    lemma_swap_preserves_permutation(v, old_v_before_swap, i, j);
                    
                    assert(0 <= i < j < v.len());
                    assert(positive(old_v_before_swap.subrange(0, i as int)));
                    assert(old_v_before_swap[j as int] >= 0);
                    assert(old_v_before_swap[i as int] < 0);
                    
                    let old_v_ref = Ghost(&old_v_before_swap);
                    lemma_subrange_positive_after_swap(v, old_v_ref@, i, j);
                }
                
                i = i + 1;
            } else {
                assert(forall|k: usize| (i + 1) <= k < v.len() ==> v[k as int] < 0);
                assert(v[i as int] < 0);
                break;
            }
        }
    }
    
    proof {
        if i < v.len() {
            assert(v[i as int] < 0);
            assert(forall|k: usize| (i + 1) <= k < v.len() ==> v[k as int] < 0);
        }
        assert(forall|u: usize| #![auto] i <= u < v.len() ==> v[u as int] < 0);
    }
    
    i
}
// </vc-code>

fn main() {}

}