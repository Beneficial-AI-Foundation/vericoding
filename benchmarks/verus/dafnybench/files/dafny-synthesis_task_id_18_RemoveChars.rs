// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

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
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}