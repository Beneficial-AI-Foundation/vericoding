use vstd::prelude::*;

verus! {
    // Insertion sort.
    //
    // Author: Snorri Agnarsson, snorri@hi.is
    // Translated to Verus

    spec fn is_sorted(s: Seq<int>) -> bool {
        forall|p: int, q: int| 0 <= p < q < s.len() ==> s[p] <= s[q]
    }

    //IMPL insertion_sort
    fn insertion_sort(s: &Vec<int>) -> (r: Vec<int>)
        ensures 
            s@.to_multiset() == r@.to_multiset(),
            is_sorted(r@),
    {
        let mut result = Vec::new();
        
        /* code modified by LLM (iteration 3): establish base case for empty result */
        assert(result@.to_multiset() == s@.subrange(0, 0).to_multiset());
        
        /* code modified by LLM (iteration 3): fixed loop invariant to match actual multiset relationship */
        for i in 0..s.len()
            invariant
                result@.len() == i,
                result@.to_multiset() == s@.subrange(0, i as int).to_multiset(),
                is_sorted(result@),
        {
            let key = s[i];
            let mut j = result.len();
            
            /* code modified by LLM (iteration 3): establish invariants before inner loop */
            assert(forall|k: int| j < k < result.len() ==> false); // vacuously true since j == result.len()
            assert(forall|k: int| 0 <= k < j ==> result[k as int] <= key || result[k as int] > key); // always true
            
            /* code modified by LLM (iteration 3): fixed inner loop invariants */
            while j > 0 && result[j - 1] > key
                invariant
                    j <= result.len(),
                    forall|k: int| j < k < result.len() ==> result[k as int] > key,
                    forall|k: int| 0 <= k <= j ==> (k == j || result[k as int] <= key),
                    is_sorted(result@),
                decreases j,
            {
                j = j - 1;
            }
            
            /* code modified by LLM (iteration 3): prove multiset preservation step by step */
            let old_result = result@;
            assert(old_result.to_multiset().insert(key) == old_result.insert(j as int, key).to_multiset());
            result.insert(j, key);
            
            /* code modified by LLM (iteration 3): prove the multiset relationship after insertion */
            assert(old_result.to_multiset() == s@.subrange(0, i as int).to_multiset());
            assert(s@.subrange(0, i as int + 1) == s@.subrange(0, i as int).push(s[i as int]));
            assert(s@.subrange(0, i as int + 1).to_multiset() == s@.subrange(0, i as int).to_multiset().insert(key));
            assert(result@.to_multiset() == s@.subrange(0, i as int + 1).to_multiset());
        }
        
        /* code modified by LLM (iteration 3): final proof that we've processed the entire sequence */
        assert(s.len() as int == s@.len());
        assert(s@.subrange(0, s@.len()) == s@);
        
        result
    }
}

fn main() {}