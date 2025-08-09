use vstd::prelude::*;

verus! {
    // Insertion sort.
    //
    // Author: Snorri Agnarsson, snorri@hi.is
    // Translated to Verus

    spec fn is_sorted(s: Seq<int>) -> bool {
        forall|p: int, q: int| 0 <= p < q < s.len() ==> s[p] <= s[q]
    }

    fn insertion_sort(s: &Vec<int>) -> (r: Vec<int>)
        ensures 
            s@.to_multiset() == r@.to_multiset(),
            is_sorted(r@),
    {
        let mut result = Vec::new();
        
        for i in 0..s.len()
            invariant
                result@.to_multiset() == s@.subrange(0, i as int).to_multiset(),
                is_sorted(result@),
        {
            let key = s[i];
            let mut j = result.len();
            
            // Find insertion position by scanning backwards
            /* code modified by LLM (iteration 1): added decreases clause for termination */
            while j > 0 && result[j - 1] > key
                invariant
                    j <= result.len(),
                    result@.to_multiset() == s@.subrange(0, i as int).to_multiset(),
                    is_sorted(result@.subrange(0, j as int)),
                    forall|k: int| j <= k < result.len() ==> result@[k] > key,
                    forall|k: int| 0 <= k < j ==> result@[k] <= result@[j as int],
                decreases j
            {
                j = j - 1;
            }
            
            // Insert the key at position j
            result.insert(j, key);
        }
        
        result
    }
}

fn main() {}