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
        if arr[i as int] % 2 == 0 {
            result.push(arr[i as int]);
        }
        i = i + 1;
    }
    
    // Assert final properties to help verification
    assert(forall|k: int| 0 <= k < arr.len() && arr[k] % 2 == 0 ==> result.contains(arr[k]));
    
    result
}

}