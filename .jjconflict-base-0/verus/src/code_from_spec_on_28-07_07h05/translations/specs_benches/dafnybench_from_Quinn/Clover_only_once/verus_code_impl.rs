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
        
        /* code modified by LLM (iteration 2): Removed curly braces around invariant clauses to fix compilation error */
        while i < a.len()
            invariant 
                0 <= i <= a.len(),
                count == count_occurrences(a@.subrange(0, i as int), key),
        {
            if a[i] == key {
                count += 1;
            }
            i += 1;
        }
        
        assert(a@.subrange(0, a.len() as int) =~= a@);
        count == 1
    }

    /* code modified by LLM (iteration 3): Removed unsupported print! statements from main function */
    fn main() {
        let arr = [1, 2, 3, 2, 4];
        let result1 = only_once(&arr, 1);
        let result2 = only_once(&arr, 2);
        let result3 = only_once(&arr, 5);
        
        // Results computed but not printed due to Verus limitations
        // result1 should be true (1 appears once)
        // result2 should be false (2 appears twice) 
        // result3 should be false (5 doesn't appear)
    }
}