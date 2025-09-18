// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Added spec fn to count non-zero elements in sequence */ spec fn count_nonzero(s: Seq<i32>) -> int {
    (|j: int| 0 <= j < s.len() && s[j] != 0).count()
}
// </vc-helpers>

// <vc-spec>
fn count_nonzero(a: Vec<i32>) -> (count: usize)
    ensures
        count <= a.len(),
        a.len() == 0 ==> count == 0,
        (forall|i: int| 0 <= i < a.len() ==> a[i] == 0) ==> count == 0,
        (forall|i: int| 0 <= i < a.len() ==> a[i] != 0) ==> count == a.len(),
        (exists|i: int| 0 <= i < a.len() && a[i] != 0) ==> count > 0,
        (exists|i: int| 0 <= i < a.len() && a[i] == 0) ==> count < a.len()
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Added semicolons after loop invariants and ensured type consistency */ 
    let mut count: u64 = 0;
    let len = a.len();
    for i in 0..len {
        invariant 0 <= i as int <= len as int;
        invariant count as int == (|j: int| 0 <= j < i as int && a@[j] != 0).count();
        invariant count as int <= i as int;
        if a[i] != 0 {
            count += 1;
            proof {
                assert(count == (|k: int| 0 <= k < i as int && a@[k] != 0).count() + 1);
                assert(count as int <= i as int);
            }
        }
    }
    proof {
        assert(count == (|j: int| 0 <= j < a.len() && a@[j] != 0).count());
        assert(count <= len);
        if len == 0 {
            assert(count == 0);
        }
        if (forall|k: int| 0 <= k < len ==> a@[k] == 0) {
            assert(count == 0);
        }
        if (forall|k: int| 0 <= k < len ==> a@[k] != 0) {
            assert(count == len);
        }
        if exists|k: int| 0 <= k < len && a@[k] != 0 {
            assert(count > 0);
        }
        if exists|k: int| 0 <= k < len && a@[k] == 0 {
            assert(count < len);
        }
    }
    count as usize
}
// </vc-code>

}
fn main() {}