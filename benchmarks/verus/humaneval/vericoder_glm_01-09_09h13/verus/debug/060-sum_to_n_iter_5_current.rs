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
proof fn lemma_sum_to_n_is_recursive(n: nat)
    decreases n
{
    if n > 0 {
        lemma_sum_to_n_is_recursive((n - 1) as nat);
        assert(spec_sum_to_n(n) == n + spec_sum_to_n((n - 1) as nat));
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
    let mut i: u32 = 0;
    let mut total: u32 = 0;
    while i < n
        invariant 
            total == spec_sum_to_n(i as nat),
            i <= n,
        decreases (n - i) as int
    {
        i = i + 1;
        let new_total = total + i;
        if new_total < total { // overflow check
            return None;
        }
        total = new_total;
        proof {
            let j = i as nat;
            lemma_sum_to_n_is_recursive(j);
            assert(spec_sum_to_n(j) == j + spec_sum_to_n((j - 1) as nat));
            assert(new_total == spec_sum_to_n(j));
        }
    }
    Some(total)
}
// </vc-code>

fn main() {}
}