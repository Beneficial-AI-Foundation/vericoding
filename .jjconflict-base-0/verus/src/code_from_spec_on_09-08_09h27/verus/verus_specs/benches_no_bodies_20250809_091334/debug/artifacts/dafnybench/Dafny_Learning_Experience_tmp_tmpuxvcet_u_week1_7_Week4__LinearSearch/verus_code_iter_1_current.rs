use vstd::prelude::*;

verus! {
    // First version of linear search - finds first element equal to target
    fn linear_search0(a: &Vec<u32>, target: u32) -> (n: usize)
        requires true,
        ensures 
            n <= a.len(),
            n < a.len() ==> a[n as int] == target,
    {
        let mut i: usize = 0;
        while i < a.len()
            invariant
                i <= a.len(),
                forall|j: int| 0 <= j < i ==> a[j] != target,
        {
            if a[i] == target {
                return i;
            }
            i += 1;
        }
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
        let mut i: usize = 0;
        while i < a.len()
            invariant
                i <= a.len(),
                forall|j: int| 0 <= j < i ==> a[j] != target,
        {
            if a[i] == target {
                return i;
            }
            i += 1;
        }
        i
    }

    // Test function
    fn test_linear_search() {
        let v = vec![1u32, 3u32, 5u32, 7u32, 9u32];
        
        // Test finding existing element
        let result0 = linear_search0(&v, 5u32);
        assert(result0 == 2);
        
        let result1 = linear_search1(&v, 5u32);
        assert(result1 == 2);
        
        // Test searching for non-existing element
        let result2 = linear_search0(&v, 6u32);
        assert(result2 == v.len());
        
        let result3 = linear_search1(&v, 6u32);
        assert(result3 == v.len());
    }

    fn main() {
        test_linear_search();
        println!("Linear search tests passed!");
    }
}