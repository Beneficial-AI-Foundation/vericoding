use vstd::prelude::*;

verus! {

// <vc-helpers>
// (No helper functions needed for this proof; kept intentionally empty)
// </vc-helpers>

// <vc-spec>
fn monotonic(l: Vec<i32>) -> (ret: bool)
    // post-conditions-start
    ensures
        ret <==> (forall|i: int, j: int| 0 <= i < j < l@.len() ==> l@.index(i) <= l@.index(j)) || (
        forall|i: int, j: int| 0 <= i < j < l@.len() ==> l@.index(i) >= l@.index(j)),
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    let mut i: nat = 0;
    let n: nat = l.len();
    let mut nondec: bool = true;
    let mut noninc: bool = true;
    while i + 1 < n
        invariant i <= n;
        invariant nondec == (forall|k: int| 0 <= k < (i as int) ==> l@.index(k) <= l@.index(k + 1));
        invariant noninc == (forall|k: int| 0 <= k < (i as int) ==> l@.index(k) >= l@.index(k + 1));
        decreases n - i;
    {
        let a_opt = l.get(i);
        let b_opt = l.get(i + 1);
        assert(a_opt.is_Some());
        assert(b_opt.is_Some());
        let a = a_opt.get_Some_0();
        let b = b_opt.get_Some_0();
        if a > b {
            nondec = false;
        }
        if a < b {
            noninc = false;
        }
        i = i + 1;
    }
    nondec || noninc
}
// </vc-code>

fn main() {}
}