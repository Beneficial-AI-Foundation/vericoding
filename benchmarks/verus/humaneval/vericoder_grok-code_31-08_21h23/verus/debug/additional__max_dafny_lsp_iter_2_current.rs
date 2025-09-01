use vstd::prelude::*;

verus! {

// <vc-helpers>
#[verifier::loop_isolation(false)]
fn max_index_seq(s: Seq<i32>) -> (x: usize)
    requires s.len() > 0
    ensures
        0 <= x < s.len(),
        forall |k: int| #![trigger s[k as nat]] 0 <= k < s.len() ==> s[k as nat] <= s[x as nat]
{
    let mut max_i: usize = 0;
    let mut i: usize = 1;
    while i < s.len() as usize
        invariant
            0 <= max_i < i || s.len() == 0,
            0 <= i <= s.len() as usize,
            forall |j: usize| #![trigger s[j as nat]]
                j < i ==> s[j as nat] <= s[max_i as nat]
    {
        if s[i as nat] > s[max_i as nat] {
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
    let s = a@;
    let mut max_i: usize = 0;
    let mut i: usize = 1;
    while i < s.len() as usize
        invariant
            0 <= max_i < i || s.len() == 0,
            0 <= i <= s.len() as usize,
            forall |j: usize| #![trigger s[j as nat]]
                j < i ==> s[j as nat] <= s[max_i as nat]
    {
        if s[i as nat] > s[max_i as nat] {
            max_i = i;
        }
        i += 1;
    }
    max_i
}
// </vc-code>

fn main() {}
}