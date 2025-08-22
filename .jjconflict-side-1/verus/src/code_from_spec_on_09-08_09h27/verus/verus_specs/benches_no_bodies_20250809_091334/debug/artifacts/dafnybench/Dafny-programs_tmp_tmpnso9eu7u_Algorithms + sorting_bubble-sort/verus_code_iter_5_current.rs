use vstd::prelude::*;

verus! {
    // Predicate to check if array is sorted between indices from and to
    // Translates Dafny's predicate sorted_between(A:array<int>, from:int, to:int)
    spec fn sorted_between(a: Seq<i32>, from: int, to: int) -> bool {
        forall|i: int, j: int| 
            0 <= i <= j < a.len() && from <= i <= j <= to ==> a[i] <= a[j]
    }

    // Predicate to check if entire array is sorted
    // Translates Dafny's predicate sorted(A:array<int>)
    spec fn sorted(a: Seq<i32>) -> bool {
        a.len() == 0 || sorted_between(a, 0, (a.len() - 1) as int)
    }

    // Test the predicates to verify they work correctly
    proof fn test_sorted_predicates() {
        // Test empty sequence
        let empty_seq: Seq<i32> = seq![];
        assert(sorted(empty_seq));
        
        // Test single element sequence
        let single_seq = seq![5];
        assert(sorted(single_seq));
        
        // Test sorted sequence
        let sorted_seq = seq![1, 2, 3, 4, 5];
        assert(sorted(sorted_seq));
        
        // Test sorted_between predicate
        let test_seq = seq![1, 3, 2, 4];
        assert(sorted_between(test_seq, 0, 1)); // [1, 3] is sorted
        assert(!sorted_between(test_seq, 1, 3)); // [3, 2, 4] is not sorted
    }

    // Bubble sort function signature with contracts
    // Note: Full implementation would require advanced Verus features
    // for mutable array operations that preserve multiset equivalence
    fn bubble_sort_spec(a: &mut Vec<i32>)
        requires old(a).len() > 0,
        ensures 
            sorted(a@),
            a@.to_multiset() == old(a)@.to_multiset(),
    {
        let n = a.len();
        let mut i = 0;
        
        /* code modified by LLM (iteration 1): added explicit trigger annotations for quantifiers */
        while i < n
            invariant 
                0 <= i <= n,
                a@.to_multiset() == old(a)@.to_multiset(),
                forall|k: int| #[trigger] a@[k] | i <= k < n ==> 
                    forall|j: int| #[trigger] a@[j] | 0 <= j < i ==> a@[j] <= a@[k],
            decreases n - i
        {
            let mut j = 0;
            
            while j < n - 1 - i
                invariant 
                    0 <= j <= n - 1 - i,
                    a@.to_multiset() == old(a)@.to_multiset(),
                    forall|k: int| #[trigger] a@[k] | i <= k < n ==> 
                        forall|l: int| #[trigger] a@[l] | 0 <= l < i ==> a@[l] <= a@[k],
                    forall|k: int| #[trigger] a@[k] | n - 1 - i < k < n ==> 
                        forall|l: int| #[trigger] a@[l] | 0 <= l <= j ==> a@[l] <= a@[k],
                decreases n - 1 - i - j
            {
                if a[j] > a[j + 1] {
                    /* code modified by LLM (iteration 1): fixed borrowing issue by storing values before swapping */
                    let temp_j = a[j];
                    let temp_j_plus_1 = a[j + 1];
                    a.set(j, temp_j_plus_1);
                    a.set(j + 1, temp_j);
                }
                j += 1;
            }
            i += 1;
        }
    }

    fn main() {
        let mut test_vec = vec![64, 34, 25, 12, 22, 11, 90];
        bubble_sort_spec(&mut test_vec);
        // Sorted vector is available in test_vec but cannot be printed in Verus
    }
}