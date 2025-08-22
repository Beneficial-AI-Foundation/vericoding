use vstd::prelude::*;

verus! {
    // (a) Recursive sum function - spec function works with ghost int
    spec fn sum(a: Seq<int>, i: int, j: int) -> int
        decreases j - i
    {
        if i >= j {
            0
        } else {
            a[i] + sum(a, i + 1, j)
        }
    }

    // Helper function to convert sequence of i32 to int
    spec fn seq_to_int(a: Seq<i32>) -> Seq<int> {
        a.map(|_idx: int, x: i32| x as int)
    }

    // (c) Predicate for prefix sum
    spec fn is_prefix_sum_for(a: Seq<int>, c: Seq<int>) -> bool {
        &&& a.len() + 1 == c.len()
        &&& c[0] == 0
        &&& forall|i: int| 0 <= i < a.len() ==> c[i + 1] == c[i] + a[i]
    }

    // Auxiliary lemma - simplified version
    proof fn aux(a: Seq<int>, c: Seq<int>, i: int, j: int)
        requires 
            0 <= i <= j <= a.len(),
            a.len() + 1 == c.len(),
            c[0] == 0,
            is_prefix_sum_for(a, c)
        ensures 
            sum(a, i, j) == c[j] - c[i]
        decreases j - i
    {
        if i >= j {
            // Base case: sum(a, i, j) == 0 and c[j] - c[i] == c[i] - c[i] == 0
            assert(sum(a, i, j) == 0);
            assert(c[j] - c[i] == 0);
        } else {
            // Inductive case: sum(a, i, j) == a[i] + sum(a, i+1, j)
            // By induction: sum(a, i+1, j) == c[j] - c[i+1]
            aux(a, c, i + 1, j);
            
            // From is_prefix_sum_for: c[i+1] == c[i] + a[i]
            // So: sum(a, i, j) == a[i] + (c[j] - c[i+1])
            //                   == a[i] + c[j] - (c[i] + a[i])
            //                   == c[j] - c[i]
            assert(c[i + 1] == c[i] + a[i]);
            assert(sum(a, i, j) == a[i] + sum(a, i + 1, j));
            assert(sum(a, i + 1, j) == c[j] - c[i + 1]);
            assert(sum(a, i, j) == a[i] + (c[j] - c[i + 1]));
            assert(sum(a, i, j) == a[i] + c[j] - (c[i] + a[i]));
            assert(sum(a, i, j) == c[j] - c[i]);
        }
    }

    // Fast query using prefix sums - executable code uses i32
    // Note: In practice, bounds checking would be needed to prevent overflow
    fn query_fast(a: &Vec<i32>, c: &Vec<i32>, i: usize, j: usize) -> (r: i32)
        requires 
            a.len() + 1 == c.len(),
            c[0] == 0,
            i <= j <= a.len(),
            is_prefix_sum_for(seq_to_int(a@), seq_to_int(c@)),
            // Bounds to prevent overflow - in practice these would be validated
            forall|k: int| 0 <= k < c@.len() ==> -1000000 <= #[trigger] c@[k] <= 1000000,
        ensures 
            r == sum(seq_to_int(a@), i as int, j as int)
    {
        proof {
            aux(seq_to_int(a@), seq_to_int(c@), i as int, j as int);
        }
        c[j] - c[i]
    }

    // Main function for testing (simplified)
    fn main() {
        // Simple test case
        let a = vec![1i32, 2i32, 3i32, 4i32];
        let c = vec![0i32, 1i32, 3i32, 6i32, 10i32];
        
        // Query sum from index 1 to 3 (elements 2, 3)
        let result = query_fast(&a, &c, 1, 3);
        assert(result == 5); // 2 + 3 = 5
    }
}