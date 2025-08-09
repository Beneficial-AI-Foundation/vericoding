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

fn sum_to_n(n: u32) -> (sum: Option<u32>)
    // post-conditions-start
    ensures
        sum.is_some() ==> sum.unwrap() == spec_sum_to_n(n as nat),
    // post-conditions-end
{
    let mut i: u32 = 0;
    let mut total: u32 = 0;
    
    /* code modified by LLM (iteration 1): added decreases clause for loop termination */
    while i < n
        invariant
            i <= n,
            total == spec_sum_to_n(i as nat),
            total <= u32::MAX,
        decreases n - i,
    {
        if total > u32::MAX - (i + 1) {
            return None;
        }
        i = i + 1;
        total = total + i;
    }
    
    Some(total)
}

}
fn main() {}