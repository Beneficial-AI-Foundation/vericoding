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
            forall|k: int| 0 <= k < i && arr[k as int] % 2 == 0 ==> result.contains(arr[k as int]),
            // Additional invariant to help with final postcondition
            forall|k: int| 0 <= k < i ==> (arr[k] % 2 == 0 <==> result.contains(arr[k]))
    {
        let current_element = arr[i as int];
        
        if current_element % 2 == 0 {
            result.push(current_element);
            
            // Prove that the new element satisfies our invariants
            assert(current_element % 2 == 0);
            assert(arr.contains(current_element));
        }
        
        i = i + 1;
        
        // Help prove the strengthened invariant is maintained
        assert(forall|k: int| 0 <= k < i ==> (arr[k] % 2 == 0 <==> result.contains(arr[k])));
    }
    
    // Final assertions to help verify postconditions
    assert(i == arr.len());
    assert(forall|k: int| 0 <= k < arr.len() ==> (arr[k] % 2 == 0 <==> result.contains(arr[k])));
    assert(forall|x: int| arr.contains(x) && x % 2 == 0 ==> result.contains(x));
    
    result
}

}