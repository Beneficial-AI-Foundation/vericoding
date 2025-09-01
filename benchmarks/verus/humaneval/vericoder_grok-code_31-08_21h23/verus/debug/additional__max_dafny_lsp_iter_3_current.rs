use vstd::prelude::*;

verus! {

// <vc-helpers>
#[verifier::loop_isolation(false)]
fn max_index_seq(s: &[i32]) -> (x: usize)
    requires s.len() > 0
    ensures
        0 <= x < s.len(),
        forall |k: int| #![trigger s@[k]] 0 <= k < s.len() ==> s@[k] <= s@[x as int]
{
    let mut max_i: usize = 0;
    let mut i: usize = 1;
    while i < s.len()
        invariant
            0 <= max_i < i || s.len() == 0,
            0 <= i <= s.len(),
            forall |j: usize| #![trigger s@[j as int]]
                j < i ==> s@[j as int] <= s@[max_i as int]
    {
        if s[i] > s[max_i] {
            max_i = i;
        }
        i += 1;
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
    let mut max_i: usize = 0;
    let mut i: usize = 1;
    while i < a.len()
        invariant
            0 <= max_i < i || a.len() == 0,
            0 <= i <= a.len(),
            forall |j: usize| #![trigger a@[j as int]]
                j < i ==> a@[j as int] <= a@[max_i as int]
    {
        if a[i] > a[max_i] {
            max_i = i;
        }
        i += 1;
    }
    max_i
}
// </vc-code>

fn main() {}
}