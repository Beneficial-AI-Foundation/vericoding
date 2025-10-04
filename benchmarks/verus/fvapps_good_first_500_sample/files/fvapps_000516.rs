// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn list_sum(a: Seq<nat>) -> nat
    decreases a.len()
{
    if a.len() == 0 {
        0
    } else {
        a[0] + list_sum(a.skip(1))
    }
}
// </vc-helpers>

// <vc-spec>
fn find_sequence(n: nat, s: nat, k: nat, m: nat, M: nat) -> (result: Option<Vec<nat>>)
    requires 
        n >= 3,
        n <= 20,
        k >= 1,
        k <= 20,
        m <= 10,
        M <= 20,
        s <= 200,
        m <= M,
        k <= n - 2,
        n * m <= s && s <= n * M,
    ensures 
        match result {
            Some(seq) => 
                seq.len() == n &&
                forall|i: int| 0 <= i < seq.len() ==> m <= seq[i] && seq[i] <= M &&
                list_sum(seq@) == s,
            None => true
        }
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume(false);
    unreached()
    // impl-end
}
// </vc-code>


}
fn main() {}