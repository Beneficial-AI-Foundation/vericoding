use vstd::prelude::*;

verus! {

// <vc-helpers>
#[verifier::loop_isolation(false)]
fn max_index_seq(s: Seq<i32>) -> (x: int)
    requires s.len() > 0
    ensures
        0 <= x < s.len(),
        forall |k: int| 0 <= k < s.len() ==> s[k] <= s[x]
{
    let mut max_i: int = 0;
    for i in 1..s.len()
        invariant
            0 <= max_i < s.len(),
            forall |j: int| #![trigger s[j]] 0 <= j < i ==> s[j] <= s[max_i]
    {
        if s[i] > s[max_i] {
            max_i = i;
        }
    }
    max_i
}
// </vc-helpers>

// <vc-spec>
#[verifier::loop_isolation(false)]
fn max_dafny_lsp(a: &[i32]) -> (x: usize)
    // pre-conditions-start
    requires
        a.len() > 0,
    // pre-conditions-end
    // post-conditions-start
    ensures
        0 <= x < a.len(),
        forall|k: int| 0 <= k < a.len() ==> a[k] <= a[x as int],
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    let max_i = max_index_seq(a@);
    (max_i as usize)
}
// </vc-code>

fn main() {}
}