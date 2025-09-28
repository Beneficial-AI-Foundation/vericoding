use vstd::prelude::*;

verus! {

// <vc-helpers>
// <vc-helpers>
// No helpers needed for this proof.
 // </vc-helpers>
// </vc-helpers>

// <vc-spec>
fn double_array_elements(s: &mut Vec<i32>)
    ensures forall|i: int| 0 <= i < old(s).len() ==> s[i] == 2 * old(s)[i]
// </vc-spec>
// <vc-code>
{
    let old_seq: Seq<i32> = s@;
    let n: nat = s.len();
    let mut i: nat = 0;
    while i < n
        invariant i <= n && s.len() == n && forall |j: nat| j < i ==> s@[j] == 2 * old_seq@[j];
        decreases n - i;
    {
        let v = old_seq@[i];
        s.set(i, 2 * v);
        i = i + 1;
    }
    proof {
        assert(i == n);
        assert(forall |j: nat| j < n ==> s@[j] == 2 * old_seq@[j]);
    }
}
// </vc-code>

fn main() {
}

}