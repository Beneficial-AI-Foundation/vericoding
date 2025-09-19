// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
spec fn bxor(a: u32, b: u32) -> u32
{
    a ^ b
}

spec fn apply_xor_to_seq(s: Seq<u32>, k: u32) -> Seq<u32>
    decreases s.len()
{
    if s.len() == 0 {
        seq![]
    } else {
        seq![bxor(s[0], k)].add(apply_xor_to_seq(s.skip(1), k))
    }
}

spec fn seqs_have_same_elements(s1: Seq<u32>, s2: Seq<u32>) -> bool
{
    s1.to_set() == s2.to_set()
}

fn find_smallest_k(n: usize, s: Vec<u32>) -> (result: i32)
    requires 
        s.len() == n,
        n >= 1,
        forall|i: int, j: int| 0 <= i < s.len() && 0 <= j < s.len() && i != j ==> s[i] != s[j],
        forall|i: int| 0 <= i < s.len() ==> s[i] < 1024,
    ensures 
        result == -1 || (result > 0 && result <= 1024),
        result != -1 ==> seqs_have_same_elements(apply_xor_to_seq(s@, result as u32), s@),
        result != -1 ==> forall|k: u32| 0 < k < result ==> !seqs_have_same_elements(apply_xor_to_seq(s@, k), s@)
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume(false);
    -1
    // impl-end
}
// </vc-code>


}
fn main() {}