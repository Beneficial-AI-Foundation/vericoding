use vstd::prelude::*;

verus! {
    // Predicate to check if all elements in a sequence are non-negative
    spec fn positive(s: Seq<u32>) -> bool {
        true  // All u32 values are non-negative
    }

    // Predicate to check if an integer is even
    spec fn isEven(i: u32) -> bool {
        i % 2 == 0
    }

    // Function to count even numbers in a sequence
    spec fn CountEven(s: Seq<u32>) -> int
        decreases s.len()
    {
        if s.len() == 0 {
            0 as int
        } else {
            let last_idx = (s.len() - 1) as int;
            (if s[last_idx] % 2 == 0 { 1 as int } else { 0 as int }) + CountEven(s.subrange(0, last_idx))
        }
    }

    // A simpler version that counts from the beginning
    spec fn CountEvenPrefix(s: Seq<u32>, len: int) -> int
        decreases len
    {
        if len <= 0 {
            0 as int
        } else {
            let idx = (len - 1) as int;
            (if s[idx] % 2 == 0 { 1 as int } else { 0 as int }) + CountEvenPrefix(s, len - 1)
        }
    }

    // Lemma showing the relationship between CountEven and CountEvenPrefix
    proof fn CountEvenEquiv(s: Seq<u32>)
        decreases s.len()
        ensures CountEven(s) == CountEvenPrefix(s, s.len() as int)
    {
        if s.len() == 0 {
            // Base case: both return 0
        } else {
            // Inductive case: prove equivalence by induction
            let sub_s = s.subrange(0, s.len() - 1);
            CountEvenEquiv(sub_s);
            // The recursive calls are equivalent by induction hypothesis
            // and both functions process the same element at the same position
        }
    }

    // Method to count even numbers in an array
    fn mcountEven(v: &[u32]) -> (n: u32)
        requires 
            positive(v@),
            v.len() <= u32::MAX
        ensures n as int == CountEven(v@)
    {
        let mut count: u32 = 0;
        let mut i: usize = 0;
        
        while i < v.len()
            invariant 
                i <= v.len(),
                count as int == CountEvenPrefix(v@, i as int),
        {
            if v[i] % 2 == 0 {
                count = count + 1;
            }
            i = i + 1;
        }
        
        proof {
            CountEvenEquiv(v@);
        }
        
        count
    }
}

fn main() {}