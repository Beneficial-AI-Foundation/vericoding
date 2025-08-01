/* code modified by LLM (iteration 1): Added import for print_u64 function */
use vstd::prelude::*;
use vstd::pervasive::print_u64;

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
        if i == j {
            // Base case: sum(a, i, i) == 0 and c[i] - c[i] == 0
        } else {
            // Inductive step
            aux(a, c, i + 1, j);
            // From the definition of is_prefix_sum_for, we know c[i+1] == c[i] + a[i]
            // So sum(a, i, j) == a[i] + sum(a, i+1, j) == a[i] + (c[j] - c[i+1]) 
            //                == a[i] + c[j] - (c[i] + a[i]) == c[j] - c[i]
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
        let a = vec![1i32, 2i32, 3i32, 4i32];
        let c = vec![0i32, 1i32, 3i32, 6i32, 10i32];
        let result = query_fast(&a, &c, 1, 3);
        print_u64(result as u64);
    }
}