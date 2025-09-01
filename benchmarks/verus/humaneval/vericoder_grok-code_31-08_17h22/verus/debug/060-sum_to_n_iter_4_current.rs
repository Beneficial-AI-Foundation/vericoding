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
// Helper specifications if needed (none required here)
// </vc-helpers>

// <vc-spec>
fn sum_to_n(n: u32) -> (sum: Option<u32>)
    // post-conditions-start
    ensures
        sum.is_some() ==> sum.unwrap() == spec_sum_to_n(n as nat),
    // post-conditions-end
// </vc-spec>
// <vc-code>
fn sum_to_n(n: u32) -> (sum: Option<u32>)
    // post-conditions-start
    ensures
        sum.is_some() ==> sum.unwrap() == spec_sum_to_n(n as nat),
    // post-conditions-end
{
    // impl-start
    if n == 0 {
        return Some(0);
    }
    let mut sum: u32 = 0;
    let mut i: u32 = 1;
    while i <= n
        invariant
            1 <= i <= n + 1,
            sum == spec_sum_to_n((i - 1) as nat),
    {
        proof { reveal(spec_sum_to_n); }
        let res = sum.checked_add(i);
        match res {
            None => { return None; }
            Some(new_sum) => { sum = new_sum; }
        }
        let i_res = i.checked_add(1);
        match i_res {
            None => { return None; }
            Some(new_i) => { i = new_i; }
        }
    }
    return Some(sum);
    // impl-end
}
// </vc-code>

fn main() {}
}