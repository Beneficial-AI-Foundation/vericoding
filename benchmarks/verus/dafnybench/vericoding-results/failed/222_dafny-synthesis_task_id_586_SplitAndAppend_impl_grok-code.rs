use vstd::prelude::*;

verus! {

// <vc-helpers>
// No helpers needed for this verification.
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
    let mut r_vec: Vec<int> = Vec::new();
    let mut i: int = 0;
    while i < (len as int)
        invariant
            i >= 0,
            i <= (len as int),
            r_vec.len() == i,
            forall |j: int| 0 <= j < i ==>
                #[trigger] r_vec@[j] == l[((j + n) as nat % len) as int],
    {
        let idx: int = ((i + n) as nat % len) as int;
        r_vec.push(l[idx]);
        i = i + 1;
    }
    r_vec.to_seq()
}
// </vc-code>

fn main() {
}

}