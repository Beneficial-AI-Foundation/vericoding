use vstd::prelude::*;

verus! {
    spec fn count_occurrences<T>(s: Seq<T>, key: T) -> nat
        decreases s.len()
    {
        if s.len() == 0 {
            0nat
        } else {
            let first_match: nat = if s[0] === key { 1nat } else { 0nat };
            first_match + count_occurrences(s.subrange(1, s.len() as int), key)
        }
    }

    fn only_once(a: &[i32], key: i32) -> (b: bool)
        ensures (count_occurrences(a@, key) == 1) <==> b
    {
        let mut count = 0;
        let mut i = 0;
        
        /* code modified by LLM (iteration 1): added decreases clause to fix compilation error */
        while i < a.len()
            invariant 
                0 <= i <= a.len(),
                count == count_occurrences(a@.subrange(0, i as int), key)
            decreases a.len() - i
        {
            if a[i] == key {
                count = count + 1;
            }
            i = i + 1;
        }
        
        count == 1
    }

    fn main() {
    }
}