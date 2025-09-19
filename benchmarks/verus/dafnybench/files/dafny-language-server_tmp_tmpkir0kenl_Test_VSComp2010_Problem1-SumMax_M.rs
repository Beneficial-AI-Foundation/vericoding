// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn M(N: i8, a: &Vec<i8>) -> (result: (i8, i8))
    requires 
        0 <= N,
        a@.len() == N as nat,
        (forall|k: int| 0 <= k && k < N as int ==> 0 <= a@[k]),
    ensures 
        result.0 as int <= N as int * result.1 as int,
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}