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
            forall|k: int| 0 <= k < i ==> (arr[k as int] % 2 == 0 ==> result.contains(arr[k as int]))
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
        // Since we processed all indices 0..arr.len(), and our invariant guarantees
        // that even elements at processed indices are in result, this follows
        assert(forall|k: int| 0 <= k < arr.len() ==> (arr[k as int] % 2 == 0 ==> result.contains(arr[k as int])));
    }
    
    result
}

}