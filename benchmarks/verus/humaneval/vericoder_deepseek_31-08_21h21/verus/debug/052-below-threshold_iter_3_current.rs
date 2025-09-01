use vstd::prelude::*;

verus! {

// <vc-helpers>
proof fn lemma_forall_index<A>(s: Seq<A>, f: spec_fn(A) -> bool, i: int)
    requires
        0 <= i < s.len(),
        forall|j: int| 0 <= j < s.len() ==> f(s[j]),
    ensures
        f(s[i]),
{
}

proof fn lemma_forall_zero_len<A>(s: Seq<A>, f: spec_fn(A) -> bool)
    requires
        s.len() == 0,
    ensures
        forall|j: int| 0 <= j < s.len() ==> f(s[j]),
{
}

spec fn seq_from_slice(l: &[i32]) -> Seq<i32>
    recommends l.len() <= 0xffff_ffff,
{
    Seq::new(l.len() as nat, |i: int| l[i] as i32)
}

spec fn all_below(s: Seq<i32>, t: i32) -> bool {
    forall|i: int| 0 <= i < s.len() ==> s[i] < t
}
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
    let mut i: usize = 0;
    let n = l.len();
    while i < n
        invariant
            forall|j: int| 0 <= j < i ==> l@[j] < t,
        decreases n - i,
    {
        if l[i] >= t {
            return false;
        }
        i = i + 1;
    }
    true
}
// </vc-code>

fn main() {}
}