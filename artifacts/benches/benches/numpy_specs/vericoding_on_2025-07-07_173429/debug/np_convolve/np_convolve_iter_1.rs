use vstd::prelude::*;

verus! {

// Helper function to express the convolution sum mathematically
spec fn convolution_sum_helper(arr1: Seq<int>, arr2: Seq<int>, n: int, i: int) -> int
    recommends
        arr1.len() > 0,
        arr2.len() > 0,
        0 <= n < arr1.len() + arr2.len() - 1,
        0 <= i <= arr1.len(),
    decreases arr1.len() - i
{
    if i >= arr1.len() {
        0
    } else if 0 <= n - i < arr2.len() {
        arr1[i] * arr2[n - i] + convolution_sum_helper(arr1, arr2, n, i + 1)
    } else {
        convolution_sum_helper(arr1, arr2, n, i + 1)
    }
}

spec fn convolution_sum(arr1: Seq<int>, arr2: Seq<int>, n: int) -> int
    recommends
        arr1.len() > 0,
        arr2.len() > 0,
        0 <= n < arr1.len() + arr2.len() - 1,
{
    convolution_sum_helper(arr1, arr2, n, 0)
}

spec fn convolve(arr1: Seq<int>, arr2: Seq<int>) -> Seq<int>
    recommends
        arr1.len() > 0,
        arr2.len() > 0,
{
    Seq::new((arr1.len() + arr2.len() - 1) as nat, |n: int| convolution_sum(arr1, arr2, n))
}

// Proof that the convolution has the expected length
proof fn convolve_length_lemma(arr1: Seq<int>, arr2: Seq<int>)
    requires
        arr1.len() > 0,
        arr2.len() > 0,
    ensures
        convolve(arr1, arr2).len() == arr1.len() + arr2.len() - 1,
{
    // The length property follows directly from Seq::new
}

}

fn main() {}