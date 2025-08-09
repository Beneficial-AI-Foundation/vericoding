use vstd::prelude::*;

verus! {

// Helper function to compute the sum over a range with a condition  
spec fn conditional_sum(arr1: Seq<int>, arr2: Seq<int>, n: int, start: int, end: int) -> int
    decreases end - start
{
    if start >= end {
        0
    } else if 0 <= start < arr1.len() && 0 <= n - start < arr2.len() {
        arr1[start] * arr2[n - start] + conditional_sum(arr1, arr2, n, start + 1, end)
    } else {
        conditional_sum(arr1, arr2, n, start + 1, end)
    }
}

// Helper function to express the convolution sum mathematically
spec fn convolution_sum(arr1: Seq<int>, arr2: Seq<int>, n: int) -> int {
    conditional_sum(arr1, arr2, n, 0, arr1.len() as int)
}

// SPEC
spec fn convolve(arr1: Seq<int>, arr2: Seq<int>) -> Seq<int> {
    Seq::new((arr1.len() + arr2.len() - 1) as nat, |n: int| convolution_sum(arr1, arr2, n))
}

}

fn main() {}