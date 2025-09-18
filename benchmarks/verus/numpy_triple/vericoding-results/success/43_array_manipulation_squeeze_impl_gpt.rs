// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
proof fn squeeze_def<T>(v: Vec<T>)
    requires v.len() == 1
    ensures squeeze(v) == v[0]
{ }

proof fn only_index_in_len1_is_zero(i: int)
    requires 0 <= i, i < 1
    ensures i == 0
{ }
// </vc-helpers>

// <vc-spec>
spec fn squeeze<T>(a: Vec<T>) -> T
    recommends a.len() == 1
{
    a[0]
}

fn squeeze_exec<T: Copy>(a: Vec<T>) -> (result: T)
    requires a.len() == 1,
    ensures 
        result == squeeze(a),
        result == a[0],
        forall|b: Vec<T>| b.len() == 1 && squeeze(a) == squeeze(b) ==> a[0] == b[0],
        forall|i: int| 0 <= i < a.len() ==> a[i] == result,
// </vc-spec>
// <vc-code>
{
    let r = a[0];
    proof {
        squeeze_def::<T>(a);
        assert(squeeze(a) == a[0]);
        assert forall|b: Vec<T>| b.len() == 1 && squeeze(a) == squeeze(b) ==> a[0] == b[0] by {
            if b.len() == 1 && squeeze(a) == squeeze(b) {
                squeeze_def::<T>(a);
                squeeze_def::<T>(b);
                assert(squeeze(b) == b[0]);
            }
        };
        assert forall|i: int| 0 <= i < a.len() ==> a[i] == r by {
            if 0 <= i && i < a.len() {
                assert(a.len() == 1);
                assert(i < 1);
                only_index_in_len1_is_zero(i);
                assert(i == 0);
            }
        };
    }
    r
}
// </vc-code>

}
fn main() {}