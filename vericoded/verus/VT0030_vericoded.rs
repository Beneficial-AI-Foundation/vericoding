// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): fixed index casts and added assertions for Seq::push properties */
proof fn seq_push_indexing<T>(s_old: Seq<T>, s_new: Seq<T>, x: T)
    requires
        s_new == s_old.push(x),
    ensures
        forall|j: int| 0 <= j < s_old.len() as int ==> s_new[j] == s_old[j],
        s_new[s_old.len() as int] == x,
{
    assert(forall|j: int| 0 <= j < s_old.len() as int ==> s_new[j] == s_old[j]) by { }
    assert(s_new[s_old.len() as int] == x) by { }
}

// </vc-helpers>

// <vc-spec>
fn ones_like<T>(a: &Vec<T>) -> (result: Vec<i32>)
    ensures
        result.len() == a.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i] == 1,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): use usize indexing with proper casts; maintain invariants and call helper after push */
    let n: usize = a.len();
    let mut v: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            0 <= i as int,
            i as int <= n as int,
            v.len() == i as nat,
            forall|j: int| 0 <= j < i as int ==> v[j] == 1i32,
        decreases (n - i) as int
    {
        let ghost old_seq: Seq<i32> = v@;
        i = i + 1;
        v.push(1i32);
        proof {
            seq_push_indexing::<i32>(old_seq, v@, 1i32);
        }
    }
    v
}
// </vc-code>

}
fn main() {}