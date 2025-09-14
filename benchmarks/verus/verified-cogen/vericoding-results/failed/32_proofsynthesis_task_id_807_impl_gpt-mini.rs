// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn check_find_first_odd(arr: &Vec<u32>, index: Option<usize>) -> (result: bool)
{
    if let Some(idx) = index {
        &&& arr@.take(idx as int) == arr@.take(idx as int).filter(|x: u32| x % 2 == 0)
        &&& arr[idx as int] % 2 != 0
    } else {
        forall|k: int| 0 <= k < arr.len() ==> (arr[k] % 2 == 0)
    }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): parity predicate for even */
spec fn is_even(x: u32) -> bool { x % 2 == 0 }

/* helper modified by LLM (iteration 5): parity predicate for odd */
spec fn is_odd(x: u32) -> bool { x % 2 != 0 }

/* helper modified by LLM (iteration 5): lemma that a prefix of even elements equals its filtered version */
proof fn prefix_all_even_filter(arr: &Vec<u32>, n: int)
    requires
        0 <= n <= arr.len() as int,
        forall|k: int| 0 <= k < n ==> arr@[k] % 2 == 0,
    ensures
        arr@.take(n) == arr@.take(n).filter(|x: u32| x % 2 == 0),
    decreases
        n,
{
    if n == 0 {
    } else {
        prefix_all_even_filter(arr, n - 1);
        // For indices < n-1 the equality follows from the inductive hypothesis
        assert(forall|j: int| 0 <= j < n - 1 ==>
            arr@.take(n - 1).filter(|x: u32| x % 2 == 0)@[j] == arr@.take(n - 1)@[j]);
        // Lift the equality to take(n) for j < n-1
        assert(forall|j: int| 0 <= j < n - 1 ==>
            arr@.take(n).filter(|x: u32| x % 2 == 0)@[j] == arr@.take(n)@[j]);
        // The last element is even by the requires, so it remains in the filtered sequence
        assert(arr@[n - 1] % 2 == 0);
        assert(arr@.take(n).filter(|x: u32| x % 2 == 0)@[n - 1] == arr@.take(n)@[n - 1]);
        // Conclude extensional equality
        assert(forall|j: int| 0 <= j < n ==>
            arr@.take(n).filter(|x: u32| x % 2 == 0)@[j] == arr@.take(n)@[j]);
        assert(arr@.take(n) == arr@.take(n).filter(|x: u32| x % 2 == 0));
    }
}

// </vc-helpers>

// <vc-spec>
fn find_first_odd(arr: &Vec<u32>) -> (index: Option<usize>)

    ensures check_find_first_odd(arr, index),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): iterate to find first odd and prove correctness using lemma */
    let mut i: usize = 0;
    while i < arr.len()
        invariant
            forall|k: int| 0 <= k < i as int ==> arr@[k] % 2 == 0,
        decreases
            arr.len() - i
    {
        if arr[i] % 2 != 0 {
            let res = Some(i);
            proof {
                // prefix property holds by invariant
                assert(forall|k: int| 0 <= k < i as int ==> arr@[k] % 2 == 0);
                prefix_all_even_filter(arr, i as int);
                assert(arr@[i as int] % 2 != 0);
                assert(check_find_first_odd(arr, res));
            }
            return res;
        }
        i += 1;
    }
    proof {
        // All elements even
        assert(forall|k: int| 0 <= k < arr.len() as int ==> arr@[k] % 2 == 0);
        prefix_all_even_filter(arr, arr.len() as int);
        assert(check_find_first_odd(arr, None));
    }
    None
}

// </vc-code>

}
fn main() {}