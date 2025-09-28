// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
fn max(a: int, b: int) -> int { if a >= b { a } else { b } }
spec fn is_last_occurrence(a: &[i32], idx: int, elem: i32) -> bool { 0 <= idx < a.len() && a[idx] == elem && forall|i: int| idx < i < a.len() ==> a[i] != elem }
// </vc-helpers>

// <vc-spec>
#[verifier::loop_isolation(false)]
fn last_position(a: &[i32], elem: i32) -> (result: usize)
    requires
        0 < a.len() < 100_000,
        exists|i: int| 0 <= i < a.len() && a[i] == elem,
    ensures
        0 <= result < a.len(),
        forall|i: int| result < i < a.len() ==> a[i] != elem,
        a[result as int] == elem,
// </vc-spec>
// <vc-code>
{
    let n = a.len();
    let mut i: usize = 0;
    let mut last: usize = 0;
    let mut found: bool = false;

    while i < n
        invariant
            i <= n,
            if found { last < i && a[last as int] == elem } else { true },
            forall|k: int| 0 <= k < i as int && a[k] == elem ==> found && k <= last as int,
        decreases n - i
    {
        if a[i] == elem {
            last = i;
            found = true;
        }
        i += 1;
    }

    proof {
        let w = choose|k: int| 0 <= k < n as int && a[k] == elem;
        assert(0 <= w && w < n as int);
        assert(a[w] == elem);
        assert(found) by {
            let k = w;
            assert(0 <= k && k < i as int);
            assert(a[k] == elem);
            assert(forall|k2: int| 0 <= k2 < i as int && a[k2] == elem ==> found && k2 <= last as int);
            assert(found && k <= last as int);
        }
    }

    last
}
// </vc-code>

}
fn main() {}