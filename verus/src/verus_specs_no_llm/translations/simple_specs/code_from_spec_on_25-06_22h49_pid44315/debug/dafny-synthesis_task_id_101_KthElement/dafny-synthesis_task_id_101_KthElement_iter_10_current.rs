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
        // Since k >= 1, we have k - 1 >= 0
        assert(k - 1 >= 0);
        // Since k <= arr.len() and arr.len() fits in usize, k - 1 < usize::MAX
        assert(k - 1 < arr.len());
        assert(arr.len() <= usize::MAX);
        assert(k - 1 <= usize::MAX);
        // The cast is safe
        assert(0 <= k - 1 <= usize::MAX);
        assert(idx == (k - 1) as usize);
        assert(idx < arr.len());
    }
    arr[idx]
}

}