use vstd::prelude::*;

verus! {

// <vc-helpers>
// No updates needed for helpers in this case
// </vc-helpers>

// <vc-spec>
// <vc-spec>
fn sum(n: u32) -> (s: u32)
    requires n >= 0
    ensures s == n * (n + 1) / 2
// </vc-spec>
// </vc-spec>

// <vc-code>
fn sum(n: u32) -> (s: u32)
    requires n >= 0
    ensures s == n * (n + 1) / 2
{
    let mut total: u32 = 0;
    let mut i: u32 = 1;
    
    while i <= n
        invariant
            i <= n + 1,
            total == (i - 1) * i / 2
    {
        total = total + i;
        i = i + 1;
    }
    
    total
}
// </vc-code>

fn main() {}

}