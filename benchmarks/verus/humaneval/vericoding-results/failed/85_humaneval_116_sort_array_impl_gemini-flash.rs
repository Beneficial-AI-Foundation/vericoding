// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn popcount(n: nat) -> nat
    decreases n
{
    if n == 0 { 0 } else { popcount(n / 2) + n % 2 }
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn sort_array(s: Vec<u8>) -> (sorted: Vec<u8>)
    ensures 
        forall|i: int, j: int| 0 <= i < j < sorted@.len() ==> popcount(sorted@[i] as nat) <= popcount(sorted@[j] as nat)
            && sorted@.len() == s@.len()
            && s@.to_multiset() == sorted@.to_multiset()
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): [Fixed compilation errors by removing `as nat` casts. `popcount` now directly takes `u8` values, which are implicitly coerced to `nat` within the `spec` function.] */
{
    let mut arr: Vec<u8> = s;
    let n = arr.len();

    if n == 0 {
        return arr; // Empty array is already sorted
    }

    let mut i: usize = 0;
    while i < n
        invariant
            0 <= i as int && i as int <= n as int,
            arr.len() == n,
            arr@.to_multiset() == s@.to_multiset()
        decreases n - i
    {
        let mut j: usize = 0;
        while j < n - i - 1
            invariant
                0 <= i as int && i as int <= n as int,
                0 <= j as int && j as int <= n as int - i as int - 1,
                arr.len() == n,
                forall|k: int, l: int| n as int - i as int - 1 <= k < l < n as int ==> popcount(arr@[k] as nat) <= popcount(arr@[l] as nat),
                arr@.to_multiset() == s@.to_multiset()
            decreases n - i - 1 - j
        {
            if popcount(arr@[j]) > popcount(arr@[j+1]) {
                // Swap elements
                let temp = arr[j];
                arr.set(j, arr[j+1]);
                arr.set(j+1, temp);
            }
            j = j + 1;
        }
        i = i + 1;
    }

    arr
}
// </vc-code>


}

fn main() {}