use vstd::prelude::*;

verus! {
    // First version of linear search - finds first element equal to target
    fn linear_search0(a: &Vec<u32>, target: u32) -> (n: usize)
        requires true,
        ensures 
            n <= a.len(),
            n < a.len() ==> a[n as int] == target,
            /* code modified by LLM (iteration 3): added postcondition to ensure we find the first occurrence */
            n < a.len() ==> (forall|i: int| 0 <= i < n ==> a[i] != target),
    {
        let mut i = 0;
        /* code modified by LLM (iteration 3): strengthened loop invariant to maintain that no element before i equals target */
        while i < a.len()
            invariant 
                i <= a.len(),
                forall|j: int| 0 <= j < i ==> a[j] != target,
            decreases a.len() - i,
        {
            if a[i] == target {
                /* code modified by LLM (iteration 3): added assertion to help verifier understand postcondition is satisfied */
                assert(a[i as int] == target);
                assert(forall|j: int| 0 <= j < i ==> a[j] != target);
                return i;
            }
            i += 1;
        }
        /* code modified by LLM (iteration 3): added assertion to help verifier understand all elements checked when not found */
        assert(forall|j: int| 0 <= j < i ==> a[j] != target);
        assert(i == a.len());
        i
    }

    // Enhanced version with stronger postcondition  
    fn linear_search1(a: &Vec<u32>, target: u32) -> (n: usize)
        requires true,
        ensures 
            n <= a.len(),
            n < a.len() ==> a[n as int] == target,
            n == a.len() ==> (forall|i: int| 0 <= i < a.len() ==> a[i] != target),
    {
        let mut i = 0;
        /* code modified by LLM (iteration 3): added decreases clause to prove loop termination */
        while i < a.len()
            invariant 
                i <= a.len(),
                forall|j: int| 0 <= j < i ==> a[j] != target,
            decreases a.len() - i,
        {
            if a[i] == target {
                /* code modified by LLM (iteration 3): added assertion to help verifier understand postcondition is satisfied */
                assert(a[i as int] == target);
                return i;
            }
            i += 1;
        }
        /* code modified by LLM (iteration 3): added assertion to help verifier understand postcondition when not found */
        assert(i == a.len());
        assert(forall|j: int| 0 <= j < a.len() ==> a[j] != target);
        i
    }

    // Test function
    fn test_linear_search() {
        let v = vec![1, 3, 5, 7, 9];
        let result1 = linear_search0(&v, 5);
        /* code modified by LLM (iteration 3): added intermediate assertion to help verifier */
        assert(v[2] == 5);
        assert(result1 == 2);
        
        let result2 = linear_search0(&v, 10);
        assert(result2 == 5);
        
        let result3 = linear_search1(&v, 7);
        assert(result3 == 3);
        
        let result4 = linear_search1(&v, 2);
        assert(result4 == 5);
    }

    /* code modified by LLM (iteration 3): removed println! statement as it's not supported in Verus */
    fn main() {
        test_linear_search();
    }
}