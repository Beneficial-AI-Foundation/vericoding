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
            let val = s[i];
            let mut j = 0;
            
            /* code modified by LLM (iteration 1): Added decreases clause for verification */
            // Find insertion position
            while j < result.len() && result[j] <= val
                invariant
                    j <= result.len(),
                    forall|k: int| 0 <= k < j ==> result@[k] <= val,
                decreases result.len() - j,
            {
                j += 1;
            }
            
            // Insert val at position j
            result.insert(j, val);
        }
        
        result
    }
}

fn main() {}