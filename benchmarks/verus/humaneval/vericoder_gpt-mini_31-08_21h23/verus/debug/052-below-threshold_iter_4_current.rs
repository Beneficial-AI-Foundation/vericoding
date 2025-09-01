use vstd::prelude::*;

verus! {

// <vc-helpers>
// No helpers needed.
// </vc-helpers>

// <vc-spec>
fn below_threshold(l: &[i32], t: i32) -> (result: bool)
    // post-conditions-start
    ensures
        result == forall|i: int| 0 <= i < l.len() ==> l[i] < t,
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    let n: nat = l.len() as nat;
    let mut i: nat = 0;
    let mut ok: bool = true;
    while i < n
        invariant i <= n;
        invariant ok == (forall |j: nat| j < i ==> l[j as usize] < t);
        invariant n == l.len() as nat;
        decreases n - i
    {
        ok = ok && (l[i as usize] < t);
        i = i + 1;
    }
    assert(i == n);
    ok
}
// </vc-code>

fn main() {}
}