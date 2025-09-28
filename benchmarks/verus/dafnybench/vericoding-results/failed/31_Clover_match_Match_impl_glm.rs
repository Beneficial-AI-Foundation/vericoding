use vstd::prelude::*;

verus! {

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn match_strings(s: Seq<char>, p: Seq<char>) -> (b: bool)
  requires s.len() == p.len()
  ensures b == (forall|n: int| 0 <= n < s.len() ==> s[n] == p[n] || p[n] == '?')
// </vc-spec>
// <vc-code>
{
    let mut i: int = 0;
    while i < s.len()
        invariant 0 <= i <= s.len(),
                   forall|j: int| 0 <= j < i ==> s[j] == p[j] || p[j] == '?'
    {
        if s[i] != p[i] && p[i] != '?' {
            return false;
        }
        i = i + 1;
    }
    return true;
}
// </vc-code>

fn main() {
}

}