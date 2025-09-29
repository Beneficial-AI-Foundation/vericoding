// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): added spec function and lemma proving replace behavior */
spec fn replace_val(v: i32, x: i32, y: i32) -> i32 { if v == x { y } else { v } }

proof fn replace_val_correct(v: i32, x: i32, y: i32)
    ensures
        (v == x ==> replace_val(v, x, y) == y),
        (v != x ==> replace_val(v, x, y) == v)
{
    assert(replace_val(v, x, y) == if v == x { y } else { v });
}
// </vc-helpers>

// <vc-spec>
#[verifier::loop_isolation(false)]
fn replace(a: &mut Vec<i32>, x: i32, y: i32)
    ensures
        a.len() == old(a).len(),
        forall|k: int| 0 <= k < old(a).len() && old(a)[k] == x ==> a[k] == y,
        forall|k: int| 0 <= k < old(a).len() && old(a)[k] != x ==> a[k] == old(a)[k],
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): implement in-place replace with invariants and decreases */
    let ghost old_seq: Seq<i32> = a@;
    let old_len: usize = a.len();
    let mut i: usize = 0;
    while i < old_len
        invariant
            a.len() == old_len,
            old_len as int == old_seq.len(),
            a@.len() == old_seq.len(),
            0 <= i as int <= old_seq.len(),
            forall|k: int| 0 <= k < i as int ==> (if old_seq[k] == x { a@[k] == y } else { a@[k] == old_seq[k] }),
            forall|k: int| i as int <= k < old_seq.len() ==> a@[k] == old_seq[k]
        decreases (old_len - i) as int
    {
        if a[i] == x {
            a[i] = y;
        }
        i = i + 1;
    }
}
// </vc-code>

}
fn main() {}