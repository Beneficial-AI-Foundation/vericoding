use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn reversed(arr: Vec<char>, outarr: Vec<char>) -> bool {
    arr.len() == outarr.len() && 
    forall|k: int| 0 <= k < arr.len() ==> outarr[k] == arr[(arr.len() - 1 - k) as int]
}

fn yarra(arr: Vec<char>) -> (outarr: Vec<char>)
    requires
        arr.len() > 0
    ensures
        arr.len() == outarr.len() && reversed(arr, outarr)
{
    let mut result: Vec<char> = Vec::new();
    let mut i: usize = 0;
    
    while i < arr.len()
        invariant
            i <= arr.len(),
            result.len() == i,
            forall|k: int| 0 <= k < i ==> result[k] == arr[(arr.len() - 1 - k) as int]
    {
        result.push(arr[arr.len() - 1 - i]);
        i += 1;
    }
    
    // The loop invariant with i == arr.len() gives us what we need
    assert(i == arr.len());
    assert(result.len() == arr.len());
    
    // The loop invariant ensures the reversed property holds for all valid indices
    assert(forall|k: int| 0 <= k < arr.len() ==> result[k] == arr[(arr.len() - 1 - k) as int]);
    
    // This establishes the reversed predicate
    assert(reversed(arr, result));
    
    result
}

}