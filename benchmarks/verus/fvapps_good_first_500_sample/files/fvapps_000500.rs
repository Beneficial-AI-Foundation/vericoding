// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
spec fn xor_all_except(result: Seq<u32>, i: int) -> u32
    recommends 0 <= i < result.len()
{
    if result.len() == 0 {
        0
    } else if result.len() == 1 {
        0
    } else if i == 0 {
        xor_seq(result.skip(1))
    } else if i == result.len() - 1 {
        xor_seq(result.take(result.len() - 1))
    } else {
        xor_seq(result.take(i)) ^ xor_seq(result.skip(i + 1))
    }
}

spec fn xor_seq(s: Seq<u32>) -> u32
    decreases s.len()
{
    if s.len() == 0 {
        0
    } else {
        s[0] ^ xor_seq(s.skip(1))
    }
}

fn solve_scarf_xor(n: usize, a: Vec<u32>) -> (result: Vec<u32>)
    requires 
        n >= 2,
        n % 2 == 0,
        a.len() == n,
    ensures 
        result.len() == n,
        forall|i: int| 0 <= i < n ==> xor_all_except(result@, i) == a[i],
        forall|i: int| 0 <= i < n ==> result[i] >= 0,
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume(false);
    Vec::new()
    // impl-end
}
// </vc-code>


}
fn main() {}