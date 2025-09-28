// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn xor_range(arr: Seq<u32>, i: int, j: int) -> u32;

spec fn valid_input(arr: Seq<u32>) -> bool {
    arr.len() > 0
}

spec fn is_max_xor_subarray(arr: Seq<u32>, result: u32) -> bool
    recommends valid_input(arr)
{
    exists|i: int, j: int| 0 <= i <= j < arr.len() && result == xor_range(arr, i, j) &&
    forall|i1: int, j1: int| 0 <= i1 <= j1 < arr.len() ==> 
        (xor_range(arr, i1, j1) as int) <= (result as int)
}
// </vc-preamble>

// <vc-helpers>
proof fn xor_range_properties(arr: Seq<u32>, i: int, j: int)
    requires
        0 <= i <= j < arr.len(),
    ensures
        xor_range(arr, i, i) == arr[i],
        xor_range(arr, i, j) == (xor_range(arr, i, j - 1)) ^ arr[j]
    decreases j - i
{
    if i == j {
        assert(xor_range(arr, i, i) == arr[i]);
    } else {
        xor_range_properties(arr, i, j - 1);
    }
}

// A helper function to compute the XOR sum of a subarray
spec fn xor_range(arr: Seq<u32>, i: int, j: int) -> u32
    decreases j - i
{
    if i == j {
        arr[i]
    } else if i > j {
        0
    } else {
        xor_range(arr, i, j - 1) ^ arr[j]
    }
}
// </vc-helpers>

// <vc-spec>
fn solve(arr: Vec<u32>) -> (result: u32)
    requires valid_input(arr@)
    ensures is_max_xor_subarray(arr@, result)
// </vc-spec>
// <vc-code>
{
    let n = arr.len();
    let mut max_xor: u32 = 0;
    let mut i: int = 0;

    while i < n
        invariant
            0 <= i <= n,
            forall|i_prime: int, j_prime: int| 0 <= i_prime <= j_prime < i ==> (xor_range(arr@, i_prime, j_prime) as int) <= (max_xor as int)
    {
        let mut current_xor: u32 = 0;
        let mut j: int = i;
        while j < n
            invariant
                i <= j <= n,
                0 <= i < n,
                current_xor == xor_range(arr@, i, j - 1),
                forall|i_prime: int, j_prime: int| 0 <= i_prime <= j_prime < i ==> (xor_range(arr@, i_prime, j_prime) as int) <= (max_xor as int),
                forall|j_prime: int| i <= j_prime < j ==> (xor_range(arr@, i, j_prime) as int) <= (max_xor as int)
        {
            current_xor = current_xor ^ arr@[j];
            if current_xor > max_xor {
                max_xor = current_xor;
            }
            j = j + 1;
        }
        i = i + 1;
    }
    max_xor
}
// </vc-code>


}

fn main() {}