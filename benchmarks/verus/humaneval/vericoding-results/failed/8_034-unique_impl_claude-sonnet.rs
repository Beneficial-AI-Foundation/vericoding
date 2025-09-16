// <vc-preamble>
use vstd::calc;
use vstd::prelude::*;
use vstd::seq_lib::lemma_multiset_commutative;
use vstd::seq_lib::lemma_seq_contains_after_push;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): implemented proof bodies for lemmas */
spec fn is_sorted_and_unique(v: Seq<i32>) -> bool {
    forall|i: int, j: int| 0 <= i < j < v.len() ==> v[i] < v[j]
}

spec fn contains_all_from(result: Seq<i32>, source: Seq<i32>) -> bool {
    forall|i: int| #![trigger source[i]] 0 <= i < source.len() ==> result.contains(source[i])
}

spec fn only_contains_from(result: Seq<i32>, source: Seq<i32>) -> bool {
    forall|i: int| #![auto] 0 <= i < result.len() ==> source.contains(result[i])
}

proof fn lemma_insert_preserves_contains(v: Seq<i32>, pos: int, elem: i32, old_elem: i32)
    requires 0 <= pos <= v.len()
    ensures v.contains(old_elem) ==> v.insert(pos, elem).contains(old_elem)
{
    if v.contains(old_elem) {
        let inserted = v.insert(pos, elem);
        assert(exists|k: int| 0 <= k < v.len() && v[k] == old_elem);
        assert(inserted.len() == v.len() + 1);
        assert(forall|i: int| 0 <= i < pos ==> inserted[i] == v[i]);
        assert(inserted[pos] == elem);
        assert(forall|i: int| pos < i < inserted.len() ==> inserted[i] == v[i - 1]);
    }
}

proof fn lemma_insert_contains_new(v: Seq<i32>, pos: int, elem: i32)
    requires 0 <= pos <= v.len()
    ensures v.insert(pos, elem).contains(elem)
{
    let inserted = v.insert(pos, elem);
    assert(inserted[pos] == elem);
    assert(0 <= pos < inserted.len());
}
// </vc-helpers>

// <vc-spec>
fn unique(s: Vec<i32>) -> (result: Vec<i32>)

    ensures
        forall|i: int, j: int| 0 <= i < j < result.len() ==> result[i] < result[j],
        forall|i: int| #![auto] 0 <= i < result.len() ==> s@.contains(result[i]),
        forall|i: int| #![trigger s[i]] 0 <= i < s.len() ==> result@.contains(s[i]),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): simplified invariants and fixed loop logic */
    let mut result = Vec::new();
    let mut i = 0;
    
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            is_sorted_and_unique(result@),
            only_contains_from(result@, s@),
            forall|k: int| 0 <= k < i ==> result@.contains(s[k]),
        decreases s.len() - i
    {
        let current = s[i];
        let mut found = false;
        let mut j = 0;
        
        while j < result.len()
            invariant
                0 <= j <= result.len(),
                found ==> result@.contains(current),
                !found ==> !result@.subrange(0, j as int).contains(current),
            decreases result.len() - j
        {
            if result[j] == current {
                found = true;
                break;
            }
            j += 1;
        }
        
        if !found {
            let mut insert_pos = 0;
            while insert_pos < result.len() && result[insert_pos] < current
                invariant
                    0 <= insert_pos <= result.len(),
                    forall|k: int| 0 <= k < insert_pos ==> result[k] < current,
                decreases result.len() - insert_pos
            {
                insert_pos += 1;
            }
            
            proof {
                lemma_insert_contains_new(result@, insert_pos as int, current);
                let old_result = result@;
                lemma_insert_preserves_contains(result@, insert_pos as int, current, current);
                assert(forall|k: int| 0 <= k < i ==> old_result.contains(s[k]));
                assert(forall|k: int| 0 <= k < i ==> old_result.insert(insert_pos as int, current).contains(s[k]));
            }
            
            result.insert(insert_pos, current);
        }
        
        i += 1;
    }
    
    result
}
// </vc-code>

}
fn main() {}