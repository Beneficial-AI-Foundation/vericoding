// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn decode_cyclic(s: &Vec<i8>) -> (res: Vec<i8>)
    ensures 
        s.len() == res.len(),
        forall|i: int| s@.len() - s@.len() % 3 <= i < s@.len() ==> res@[i] == s@[i],
        forall|i: int| 0 <= i < s@.len() - s@.len() % 3 ==> (i % 3 == 0 ==> res@[i] == s@[i + 2]),
        forall|i: int| 0 <= i < s@.len() - s@.len() % 3 ==> (i % 3 == 1 ==> res@[i] == s@[i - 1])
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>


}

fn main() {}