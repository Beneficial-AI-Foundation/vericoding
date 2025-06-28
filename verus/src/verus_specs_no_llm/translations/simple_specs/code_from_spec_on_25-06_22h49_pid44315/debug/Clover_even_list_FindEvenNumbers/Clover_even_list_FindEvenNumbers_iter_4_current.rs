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
    let mut i: usize = 0;
    
    while i < arr.len()
        invariant
            0 <= i <= arr.len(),
            forall|j: int| 0 <= j < result.len() ==> result[j] % 2 == 0,
            forall|x: int| result.contains(x) ==> arr.contains(x),
            forall|k: int| 0 <= k < i && arr[k as int] % 2 == 0 ==> result.contains(arr[k as int])
    {
        let current_element = arr[i as int];
        
        if current_element % 2 == 0 {
            result.push(current_element);
            
            // Prove that the new element maintains invariants
            assert(current_element % 2 == 0);
            assert(arr.contains(current_element)) by {
                assert(0 <= i < arr.len());
                assert(arr[i as int] == current_element);
            }
        }
        
        i = i + 1;
    }
    
    // Prove the final postconditions
    assert(forall|j: int| 0 <= j < result.len() ==> result[j] % 2 == 0);
    assert(forall|x: int| result.contains(x) ==> arr.contains(x));
    
    // Prove that all even elements from arr are in result
    assert(forall|x: int| arr.contains(x) && x % 2 == 0 ==> result.contains(x)) by {
        assert(forall|k: int| 0 <= k < arr.len() && arr[k as int] % 2 == 0 ==> result.contains(arr[k as int]));
        // For any x in arr with x % 2 == 0, there exists some index k where arr[k] == x
        // and by our loop invariant, result.contains(arr[k]) which means result.contains(x)
    }
    
    result
}

}