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
        let mut i = 0;
        
        while i < arr.len()
            invariant
                0 <= i <= arr.len(),
                forall|k: int| 0 <= k < result@.len() ==> is_even_spec(result@[k] as int),
                forall|k: int| 0 <= k < result@.len() ==> arr@.contains(result@[k]),
                forall|x: i32| result@.contains(x) ==> (arr@.contains(x) && is_even_spec(x as int))
        {
            let val = arr[i];
            if val % 2 == 0 {
                result.push(val);
            }
            i += 1;
        }
        
        result
    }
}

fn main() {}