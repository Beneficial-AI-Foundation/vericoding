use vstd::prelude::*;

verus! {

// <vc-helpers>
// helper functions: none
// </vc-helpers>

// <vc-spec>
fn split_and_append(l: Seq<int>, n: int) -> (r: Seq<int>)
    requires 
        n >= 0 && n < l.len(),
    ensures 
        r.len() == l.len(),
        forall|i: int| 0 <= i < l.len() ==> r[i] == l[((i + n) as nat % l.len()) as int],
// </vc-spec>
// <vc-code>
{
    let len: nat = l.len();
    let n_nat: nat = n as nat;
    assert(n_nat < len);
    let mut v = Vec::<int>::new();
    let mut i: nat = 0;
    while i < len
        invariant i <= len;
        invariant v.len() == i;
        invariant forall |j: nat| j < i ==> v@[j] == l[((j + n_nat) % len) as int];
        decreases len - i;
    {
        let idx_nat: nat = (i + n_nat) % len;
        v.push(l[idx_nat as int]);
        i += 1;
    }
    v.into_seq()
}
// </vc-code>

fn main() {
}

}