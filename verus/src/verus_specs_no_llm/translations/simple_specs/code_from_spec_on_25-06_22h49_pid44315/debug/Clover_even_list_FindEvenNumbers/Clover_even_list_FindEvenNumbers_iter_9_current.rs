use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn FindEvenNumbers(arr: Vec<int>) -> (evenNumbers: Vec<int>)
    ensures
        forall|i: int| 0 <= i < evenNumbers.len() ==> evenNumbers[i] % 2 == 0,
        forall|x: int| evenNumbers.contains(x) ==> arr.contains(x),
        forall|x: int| arr.contains(x) && x % 2 == 0 ==> evenNumbers.contains(x)
{
    let mut result: Vec<int> = Vec::new();
    let mut i: int = 0;
    
    while i < arr.len()
        invariant
            0 <= i <= arr.len(),
            forall|j: int| 0 <= j < result.len() ==> result[j] % 2 == 0,
            forall|x: int| result.contains(x) ==> arr.contains(x),
            forall|k: int| 0 <= k < i ==> (arr[k] % 2 == 0 ==> result.contains(arr[k]))
    {
        let current_element = arr[i];
        
        if current_element % 2 == 0 {
            // Prove that pushing an even number maintains the invariant
            assert(current_element % 2 == 0);
            
            // Prove that the element being added is from the original array
            assert(arr.contains(current_element)) by {
                assert(arr[i] == current_element);
                assert(0 <= i < arr.len());
            }
            
            result.push(current_element);
            
            // Help verification understand the new result state after push
            assert(forall|j: int| 0 <= j < result.len() - 1 ==> result[j] % 2 == 0);
            assert(result[result.len() - 1] == current_element);
            assert(current_element % 2 == 0);
            assert(forall|j: int| 0 <= j < result.len() ==> result[j] % 2 == 0);
            
            // Prove all elements in result are from arr
            assert(forall|x: int| result.contains(x) ==> arr.contains(x));
        }
        
        i = i + 1;
        
        // Strengthen the invariant for the next iteration
        assert(forall|k: int| 0 <= k < i ==> (arr[k] % 2 == 0 ==> result.contains(arr[k]))) by {
            if i > 0 {
                let prev_i = i - 1;
                assert(forall|k: int| 0 <= k < prev_i ==> (arr[k] % 2 == 0 ==> result.contains(arr[k])));
                if arr[prev_i] % 2 == 0 {
                    assert(result.contains(arr[prev_i]));
                }
            }
        }
    }
    
    // After the loop, prove the postconditions
    assert(i == arr.len());
    
    // The third postcondition follows from the loop invariant
    assert(forall|x: int| arr.contains(x) && x % 2 == 0 ==> result.contains(x)) by {
        assert(forall|k: int| 0 <= k < arr.len() ==> (arr[k] % 2 == 0 ==> result.contains(arr[k])));
        // For any x in arr that is even, there exists an index k such that arr[k] == x
        // and since we processed all indices, result.contains(x) must hold
        assert(forall|x: int| arr.contains(x) ==> exists|k: int| 0 <= k < arr.len() && arr[k] == x);
    }
    
    result
}

}