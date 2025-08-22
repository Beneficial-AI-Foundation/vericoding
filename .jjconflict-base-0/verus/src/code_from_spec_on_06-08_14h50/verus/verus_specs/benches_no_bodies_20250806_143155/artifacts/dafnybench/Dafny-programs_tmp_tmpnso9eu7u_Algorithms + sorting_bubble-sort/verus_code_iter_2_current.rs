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
        let sorted_seq = seq![1, 2, 3, 4, 5];
        assert(sorted(sorted_seq));
        
        let unsorted_seq = seq![5, 4, 3, 2, 1];
        assert(!sorted(unsorted_seq));
        
        // Test sorted_between
        let partial_seq = seq![3, 1, 2, 4, 5];
        assert(sorted_between(partial_seq, 2, 4)); // indices 2,3,4 contain [2,4,5]
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
        
        while i < n
            invariant
                0 <= i <= n,
                a@.to_multiset() == old(a)@.to_multiset(),
                a@.len() == old(a)@.len(),
                forall|k: int| i <= k < n ==> 
                    forall|j: int| 0 <= j < i ==> a@[j] <= a@[k],
        {
            let mut j = 0;
            
            while j < n - 1 - i
                invariant
                    0 <= i < n,
                    0 <= j <= n - 1 - i,
                    a@.to_multiset() == old(a)@.to_multiset(),
                    a@.len() == old(a)@.len(),
                    forall|k: int| i <= k < n ==> 
                        forall|l: int| 0 <= l < i ==> a@[l] <= a@[k],
                    forall|k: int| j < k < n - i ==> a@[k - 1] <= a@[k],
            {
                if a[j] > a[j + 1] {
                    let temp = a[j];
                    a.set(j, a[j + 1]);
                    a.set(j + 1, temp);
                }
                j += 1;
            }
            i += 1;
        }
    }

    fn main() {
        /* code modified by LLM (iteration 1): removed println! macro call as it's not supported in Verus */
        let mut test_vec = vec![64, 34, 25, 12, 22, 11, 90];
        bubble_sort_spec(&mut test_vec);
        // Sorted array is now in test_vec but we cannot print it in Verus
    }
}