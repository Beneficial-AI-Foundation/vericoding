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
    let mut i: usize = 0;
    while i < s.len()
        invariant 
            0 <= i <= s.len(),
            forall|n: int| 0 <= n < i ==> s[n] == p[n] || p[n] == '?'
    {
        if s[i as int] != p[i as int] && p[i as int] != '?' {
            assert(!(s[i as int] == p[i as int] || p[i as int] == '?'));
            return false;
        }
        i = i + 1;
    }
    true
}
// </vc-code>

fn main() {
}

}