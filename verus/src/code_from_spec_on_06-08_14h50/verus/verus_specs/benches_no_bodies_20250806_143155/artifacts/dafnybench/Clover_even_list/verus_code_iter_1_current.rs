use vstd::prelude::*;

verus! {
    spec fn is_even_spec(x: int) -> bool {
        x % 2 == 0
    }

    fn find_even_numbers(arr: &[i32]) -> (even_numbers: Vec<i32>)
        requires arr.len() <= usize::MAX,
        ensures
            // All numbers in the output are even
            forall|k: int| 0 <= k < even_numbers@.len() ==> is_even_spec(even_numbers@[k] as int),
            // All numbers in the output come from the input array
            forall|k: int| 0 <= k < even_numbers@.len() ==> arr@.contains(even_numbers@[k]),
            // The output contains only even numbers from the input
            forall|x: i32| even_numbers@.contains(x) ==> (arr@.contains(x) && is_even_spec(x as int))
    {
        let mut result = Vec::new();
        
        for i in 0..arr.len()
            invariant
                // All numbers in result so far are even
                forall|k: int| 0 <= k < result@.len() ==> is_even_spec(result@[k] as int),
                // All numbers in result come from the first i elements of arr
                forall|k: int| 0 <= k < result@.len() ==> exists|j: int| 0 <= j < i && arr@[j] == result@[k],
                // Result contains only even numbers from the first i elements
                forall|x: i32| result@.contains(x) ==> (exists|j: int| 0 <= j < i && arr@[j] == x) && is_even_spec(x as int)
        {
            if arr[i] % 2 == 0 {
                result.push(arr[i]);
            }
        }
        
        result
    }
}

fn main() {}