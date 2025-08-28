use vstd::prelude::*;

verus! {

// <vc-helpers>
// No changes needed in helpers for this fix
// </vc-helpers>

// <vc-spec>
// <vc-spec>
fn match_strings(s: Seq<char>, p: Seq<char>) -> (b: bool)
  requires s.len() == p.len()
  ensures b == (forall|n: int| 0 <= n < s.len() ==> s[n] == p[n] || p[n] == '?')
// </vc-spec>
// </vc-spec>

// <vc-code>
fn match_strings(s: Seq<char>, p: Seq<char>) -> (b: bool)
    requires s.len() == p.len()
    ensures b == (forall|n: int| 0 <= n < s.len() ==> s[n] == p[n] || p[n] == '?')
{
    let mut i: usize = 0;
    let mut matches = true;

    while i < s.len()
        invariant
            0 <= i <= s.len(),
            matches == (forall|n: int| 0 <= n < i ==> s[n] == p[n] || p[n] == '?')
    {
        if s[i] != p[i] && p[i] != '?' {
            matches = false;
            break;
        }
        i = i + 1;
    }

    matches
}
// </vc-code>

fn main() {
}

}