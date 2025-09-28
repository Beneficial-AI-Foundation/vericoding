// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
proof fn helper_trivial()
    ensures
        true,
{
}

// </vc-helpers>

// <vc-spec>
fn numpy_insert<T>(arr: Vec<T>, idx: usize, value: T) -> (result: Vec<T>)
    requires idx <= arr.len(),
    ensures 
        result.len() == arr.len() + 1,

        forall|i: int| 0 <= i < idx ==> result[i] == arr[i],

        result[idx as int] == value,

        forall|i: int| (idx as int) < i < result.len() ==> result[i] == arr[i - 1],

        forall|j: int| 0 <= j < arr.len() ==> 
            (j < idx && result[j] == arr[j]) || 
            (j >= idx && result[j + 1] == arr[j])
// </vc-spec>
// <vc-code>
{
    let mut v = arr;
    v.insert(idx, value);
    v
}
// </vc-code>

}
fn main() {}