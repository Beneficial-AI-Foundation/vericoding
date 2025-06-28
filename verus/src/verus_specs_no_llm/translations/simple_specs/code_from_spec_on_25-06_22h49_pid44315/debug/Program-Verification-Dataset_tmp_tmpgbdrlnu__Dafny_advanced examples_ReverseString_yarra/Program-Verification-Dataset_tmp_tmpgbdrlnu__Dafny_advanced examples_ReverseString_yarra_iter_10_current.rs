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
            forall|k: int| 0 <= k < i ==> result[k as int] == arr[arr.len() - 1 - k]
    {
        let len = arr.len();
        let reverse_idx = len - 1 - i;
        
        result.push(arr[reverse_idx]);
        i += 1;
    }
    
    assert(result.len() == arr.len());
    assert(forall|k: int| 0 <= k < arr.len() ==> result[k] == arr[arr.len() - 1 - k]) by {
        assert(i == arr.len());
        assert(forall|k: int| 0 <= k < i ==> result[k as int] == arr[arr.len() - 1 - k]);
        assert(forall|k: int| 0 <= k < arr.len() ==> result[k as int] == arr[arr.len() - 1 - k]);
    }
    
    result
}

}