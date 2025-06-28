use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn reversed(arr: Vec<char>, outarr: Vec<char>) -> bool {
    arr.len() == outarr.len() && 
    forall|k: int| 0 <= k < arr.len() ==> outarr[k] == arr[arr.len() - 1 - k]
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
            forall|k: int| 0 <= k < i ==> result[k] == arr[arr.len() - 1 - k]
    {
        // Calculate the reverse index more carefully
        let len = arr.len();
        let reverse_idx = len - 1 - i;
        
        // Add explicit bounds assertions
        assert(len > 0);
        assert(i < len);
        assert(len >= 1);
        assert(i <= len - 1);
        assert(reverse_idx < len);
        
        result.push(arr[reverse_idx]);
        i += 1;
    }
    
    // Final assertions to help verification
    assert(result.len() == arr.len());
    assert(forall|k: int| 0 <= k < arr.len() ==> result[k] == arr[arr.len() - 1 - k]) by {
        // The loop invariant with i == arr.len() gives us this property
    }
    
    result
}

}