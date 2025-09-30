// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
proof fn lemma_squeeze_len1_index0<T>(v: Vec<T>)
    requires
        v.len() == 1,
    ensures
        squeeze(v) == v[0],
{
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
    let x = a[0];

    assert(x == squeeze(a)) by {
        lemma_squeeze_len1_index0::<T>(a);
    };

    assert forall|b: Vec<T>| b.len() == 1 && squeeze(a) == squeeze(b) ==> a[0] == b[0] by {
        if b.len() == 1 && squeeze(a) == squeeze(b) {
            lemma_squeeze_len1_index0::<T>(a);
            lemma_squeeze_len1_index0::<T>(b);
            assert(squeeze(a) == a[0]);
            assert(squeeze(b) == b[0]);
            assert(a[0] == b[0]);
        }
    };

    assert forall|i: int| 0 <= i < a.len() ==> a[i] == x by {
        if 0 <= i && i < a.len() {
            assert(a.len() == 1);
            assert(i < 1);
            assert(i <= 0);
            assert(i == 0);
            assert(a[i] == a[0]);
            assert(a[0] == x);
        }
    };

    x
}

// </vc-code>

}
fn main() {}