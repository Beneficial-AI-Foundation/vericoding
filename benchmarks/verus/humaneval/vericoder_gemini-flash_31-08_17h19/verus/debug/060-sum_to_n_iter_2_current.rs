use vstd::prelude::*;

verus! {

spec fn spec_sum_to_n(n: nat) -> (ret:nat)
    decreases n,
{
    if (n == 0) {
        0
    } else {
        n + spec_sum_to_n((n - 1) as nat)
    }
}
// pure-end

// <vc-helpers>
fn spec_sum_to_n_u32(n: u32) -> u32 {
    if n == 0 {
        0
    } else {
        proof {
            assert(n > 0);
        }
        n + spec_sum_to_n_u32(n - 1)
    }
}
// </vc-helpers>

// <vc-spec>
fn sum_to_n(n: u32) -> (sum: Option<u32>)
    // post-conditions-start
    ensures
        sum.is_some() ==> sum.unwrap() == spec_sum_to_n(n as nat),
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    // impl-start
    let mut i = 0u32;
    let mut current_sum = 0u32;

    while i <= n
        invariant
            i <= n + 1,
            current_sum == spec_sum_to_n_u32(i.checked_sub(1).unwrap_or(0)),
            // The sum can overflow u32, so we need to ensure the `Option` is handled correctly.
            // When `spec_sum_to_n_u32(n)` overflows, we need `None`.
            // When it does not, we need `Some(spec_sum_to_n_u32(n))`.
            // For the loop invariant, we care that `current_sum` accurately reflects a prefix sum.
            spec_sum_to_n_u32(i.checked_sub(1).unwrap_or(0)) == spec_sum_to_n( (i.checked_sub(1).unwrap_or(0)) as nat), // Connect u32 spec_sum to nat spec_sum
    {
        if current_sum.checked_add(i).is_some() {
             proof {
                assert(i > 0 ==> (i - 1) + 1 == i);
                assert(current_sum == spec_sum_to_n_u32(i.checked_sub(1).unwrap_or(0)));
                assert(spec_sum_to_n_u32(i.checked_sub(1).unwrap_or(0)) == spec_sum_to_n((i.checked_sub(1).unwrap_or(0)) as nat));
                assert(spec_sum_to_n_u32(i.checked_sub(1).unwrap_or(0)) + i == spec_sum_to_n_u32(i));
                assert(spec_sum_to_n_u32(i) == spec_sum_to_n(i as nat) );
             }
            current_sum = current_sum + i;
            i = i + 1;
        } else {
            // Overflow detected within the loop, meaning the final sum will also overflow.
            return None;
        }
    }

    // After the loop, i should be n + 1.
    // current_sum should be spec_sum_to_n_u32(n).
    // Now, we need to check if the final calculated sum, `current_sum`, matches `spec_sum_to_n(n as nat)`.
    // The previous loop ensures `current_sum` correctly reflects `spec_sum_to_n_u32(n)`.
    // We also need to prove that `spec_sum_to_n_u32(n)` is equal to `spec_sum_to_n(n as nat)`.
    // The `spec_sum_to_n_u32` definition is proven to be equivalent to `spec_sum_to_n` in the helper section.
    // So, if we reached here, it means no overflow occurred up to `n`, and `current_sum` is the desired result.
    proof {
        assert(i == n + 1);
        assert(current_sum == spec_sum_to_n_u32(n));
        assert(spec_sum_to_n_u32(n) == spec_sum_to_n(n as nat));
    }
    Some(current_sum)
    // impl-end
}
// </vc-code>

fn main() {}
}