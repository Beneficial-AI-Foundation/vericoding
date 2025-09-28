use vstd::prelude::*;

verus! {

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn remove_chars(s1: Seq<char>, s2: Seq<char>) -> (v: Seq<char>)
    ensures 
        v.len() <= s1.len(),
        forall|i: int| 0 <= i < v.len() ==> s1.contains(v[i]) && !s2.contains(v[i]),
        forall|i: int| 0 <= i < s1.len() ==> s2.contains(s1[i]) || v.contains(s1[i])
// </vc-spec>
// <vc-code>
{
decreases s1.len() - i;
    let mut v: Seq<char> = Seq::empty();
    let mut i: int = 0;
    while i < s1.len()
        decreases s1.len() - i;
        invariant 0 <= i <= s1.len()
        invariant v.len() <= i
        invariant forall|k: int| 0 <= k < v.len() ==> #[trigger] s1.contains(v[k]) && !#[trigger] s2.contains(v[k])
        invariant forall|k: int| 0 <= k < i ==> #[trigger] (s2.contains(s1[k]) || v.contains(s1[k]))
    {
        if !s2.contains(s1[i]) {
            v = v.push(s1[i]);
        }
        i = i + 1;
    }
    v
}
// </vc-code>

fn main() {
}

}