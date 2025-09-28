// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): The `integer_sqrt` helper function now correctly handles `n = 0` and ensures `mid > 0` before checking `mid > n / mid` to avoid division by zero. The invariant conditions were refined to include `ans * ans <= n` and `(ans + 1) * (ans + 1) > n || (high < low)` to more accurately reflect the state of the binary search. The `low` initialization was set to `0` and a specific case for `n = 0` was added to ensure correct behavior. */
fn integer_sqrt(n: u64) -> (root: u64)
    requires
        n >= 0,
    ensures
        root * root <= n,
        (root + 1) * (root + 1) > n,
        root >= 0,
{
    if n == 0 {
        return 0u64;
    }

    let mut low: u64 = 0;
    let mut high: u64 = n;
    let mut ans: u64 = 0;

    while low <= high
        invariant
            low >= 0,
            high >= 0,
            high <= n,
            ans >= 0,
            ans * ans <= n,
            (ans + 1) * (ans + 1) > n || high < low,
    {
        let mid: u64 = low + (high - low) / 2;
        if mid > 0 && mid > n / mid {
            high = mid - 1;
        } else if mid * mid <= n {
            ans = mid;
            low = mid + 1;
        } else {
            high = mid - 1;
        }
    }
    ans
}
// </vc-helpers>

// <vc-spec>
fn sqrt(x: Vec<i8>) -> (result: Vec<i8>)
    ensures 
        result@.len() == x@.len(),
        forall|i: int| 0 <= i < x@.len() ==> {
            &&& (x@[i] >= 0 ==> result@[i] * result@[i] == x@[i] && result@[i] >= 0)
            &&& (x@[i] == 0 ==> result@[i] == 0)
            &&& (x@[i] == 1 ==> result@[i] == 1)
        }
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): This code now correctly handles `Seq<i8>` indexing by using an explicit cast to `int` for `x@.len()` and `x@[i]` to match the type of `i`. The `val_at_i` is cast to `u64` before calling `integer_sqrt` to avoid type mismatches. Furthermore, the `sqrt_val_u64` from `integer_sqrt` is properly cast back to `i8` before being pushed into the `result` vector. The loop invariants were adjusted to reflect the change from `nat` to `int` for `i` and `x@.len()`. */
{
    let mut result: Vec<i8> = Vec::new();
    let mut i: int = 0;

    while i < x@.len() as int
        invariant
            x@.len() == result@.len() + (x@.len() - i as nat),
            result@.len() == i as nat,
            0 <= i,
            i <= x@.len() as int,
            forall|j: int| 0 <= j < i ==> {
                &&& (x@[j as nat] >= 0 ==> result@[j as nat] * result@[j as nat] == x@[j as nat] && result@[j as nat] >= 0)
                &&& (x@[j as nat] == 0 ==> result@[j as nat] == 0)
                &&& (x@[j as nat] == 1 ==> result@[j as nat] == 1)
            },
    {
        let val_at_i = x@[i as nat];
        if val_at_i < 0 || val_at_i > 255 {
            // Cannot compute square root for negative numbers or values exceeding u64 capacity from i8
            // For this specific problem, we assume i8 values are 0 or positive.
            // If negative, we'll just push back the original value as per spec if no sqrt is possible
            result.push(val_at_i);
        } else {
            let val_u64: u64 = val_at_i as u64;
            let sqrt_val_u64 = integer_sqrt(val_u64);
            result.push(sqrt_val_u64 as i8);
        }
        i = i + 1;
    }
    result
}
// </vc-code>


}
fn main() {}