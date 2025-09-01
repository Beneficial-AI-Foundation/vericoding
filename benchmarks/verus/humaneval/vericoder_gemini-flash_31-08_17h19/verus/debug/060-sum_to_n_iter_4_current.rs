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
fn spec_sum_to_n_u32(n: u32) -> u32
    ensures
        spec_sum_to_n_u32(n) == spec_sum_to_n(n as nat),
{
    if n == 0 {
        0
    } else {
        proof {
            assert(n > 0);
            assert(spec_sum_to_n_u32(n - 1) == spec_sum_to_n((n - 1) as nat)); // Recursive call
            assert(n as nat + spec_sum_to_n((n - 1) as nat) == spec_sum_to_n(n as nat));
            assert(n + spec_sum_to_n_u32(n - 1) == spec_sum_to_n(n as nat));
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
    let mut i = 0u32;
    let mut current_sum = 0u32;

    while i <= n
        invariant
            i <= n + 1,
            current_sum == spec_sum_to_n_u32(i.checked_sub(1).unwrap_or(0)),
            current_sum == spec_sum_to_n((i.checked_sub(1).unwrap_or(0)) as nat),
    {
        if current_sum.checked_add(i).is_some() {
            proof {
                if i > 0 {
                    assert(current_sum == spec_sum_to_n_u32(i - 1));
                    assert( (i - 1) as nat == i.checked_sub(1).unwrap_or(0) as nat );
                    assert(spec_sum_to_n_u32(i - 1) + i == spec_sum_to_n_u32(i));
                } else {
                    assert(current_sum == spec_sum_to_n_u32(0)); // current_sum is 0
                    assert(spec_sum_to_n_u32(0) + i == spec_sum_to_n_u32(i)); // 0 + 0 = 0
                }
            }
            current_sum = current_sum + i;
            i = i + 1;
        } else {
            return None;
        }
    }

    // After the loop, i should be n + 1.
    // current_sum should be spec_sum_to_n_u32(n).
    proof {
        assert(i == n + 1);
        assert(current_sum == spec_sum_to_n_u32(n));
        assert(spec_sum_to_n_u32(n) == spec_sum_to_n(n as nat));
    }
    Some(current_sum)
}
// </vc-code>

fn main() {}
}