use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn KthElement(arr: Vec<int>, k: int) -> (result: int)
    requires
        1 <= k <= arr.len()
    ensures
        result == arr.spec_index(k - 1)
{
    let idx = (k - 1) as usize;
    proof {
        assert(1 <= k <= arr.len());
        assert(0 <= k - 1 < arr.len());
        assert(k - 1 >= 0);
        assert(k - 1 < arr.len());
        // The cast is valid because k-1 >= 0 and fits in usize
        assert(idx == (k - 1) as usize);
        assert(idx < arr.len());
    }
    arr[idx]
}

}