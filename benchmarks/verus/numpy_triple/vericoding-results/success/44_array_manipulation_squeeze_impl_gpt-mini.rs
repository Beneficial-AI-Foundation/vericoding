// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
fn squeeze_def<T>(a: Vec<T>)
    requires a.len() == 1,
    ensures squeeze(a) == a[0],
{
    proof {
    }
}

fn index_of_len1_is_zero(i: int)
    requires 0 <= i && i < 1,
    ensures i == 0,
{
    proof {
        if i == 0 {
        } else {
            assert(i >= 1);
            assert(i < 1);
            assert(false);
        }
    }
}

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
    let result: T = a[0];
    proof {
        assert(result == a[0]);
        assert(result == squeeze(a));
        assert(forall|b: Vec<T>| b.len() == 1 && squeeze(a) == squeeze(b) ==> a[0] == b[0]);
        assert(forall|i: int| 0 <= i < a.len() ==> a[i] == result);
    }
    result
}
// </vc-code>

}
fn main() {}