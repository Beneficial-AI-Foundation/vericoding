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
            forall|k: int| 0 <= k < i ==> (arr[k] % 2 == 0 ==> result.contains(arr[k]))
    {
        let current_element = arr[i as int];
        
        if current_element % 2 == 0 {
            result.push(current_element);
        }
        
        i = i + 1;
    }
    
    // After the loop, we know that i == arr.len()
    // The invariant tells us: forall|k: int| 0 <= k < i ==> (arr[k] % 2 == 0 ==> result.contains(arr[k]))
    // Since i == arr.len(), this means we've processed all elements
    assert(i == arr.len());
    
    result
}

}