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
            forall|k: int| 0 <= k < i ==> (arr[k] % 2 == 0 ==> result.contains(arr[k])),
            forall|x: int| (exists|k: int| 0 <= k < i && arr[k] == x && x % 2 == 0) ==> result.contains(x)
    {
        let current_element = arr[i as int];
        
        if current_element % 2 == 0 {
            result.push(current_element);
        }
        
        i = i + 1;
    }
    
    // Final assertion to help prove the postcondition
    assert(forall|x: int| arr.contains(x) && x % 2 == 0 ==> result.contains(x)) by {
        // For any x that is in arr and even, we need to show it's in result
        // arr.contains(x) means there exists some index where arr[index] == x
        // Since we processed all indices 0..arr.len(), our invariant ensures
        // that if x is even and at some processed index, then x is in result
        assert(i == arr.len());
        assert(forall|k: int| 0 <= k < arr.len() ==> (arr[k] % 2 == 0 ==> result.contains(arr[k])));
        
        // The key insight: if arr.contains(x), then x appears at some valid index
        // and our loop processed that index, so if x is even, it's in result
        assert(forall|x: int| arr.contains(x) ==> 
            exists|k: int| 0 <= k < arr.len() && arr[k] == x);
    };
    
    result
}

}