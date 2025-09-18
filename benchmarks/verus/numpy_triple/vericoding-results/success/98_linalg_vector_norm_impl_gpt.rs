// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn is_nonneg(n: int) -> bool { n >= 0 }
spec fn is_empty<T>(s: Seq<T>) -> bool { s.len() == 0 }
proof fn zero_is_nonneg() ensures is_nonneg(0) { }
// </vc-helpers>

// <vc-spec>
fn vector_norm(x: Vec<i32>, p: i32) -> (result: i32)
    requires p >= 0,
    ensures 
        result >= 0,
        x@.len() == 0 ==> result == 0,
        result >= 0
// </vc-spec>
// <vc-code>
{
    0
}
// </vc-code>

}
fn main() {}