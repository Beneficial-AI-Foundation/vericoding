use vstd::prelude::*;

verus! {

// <vc-helpers>
// No additional helpers needed for this implementation
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
            s.len() == p.len(),
            forall|n: int| 0 <= n < i as int ==> s[n] == p[n] || p[n] == '?',
    {
        if s[i] != p[i] && p[i] != '?' {
            assert(!(s[i as int] == p[i as int] || p[i as int] == '?'));
            return false;
        }
        i += 1;
    }
    assert(i as int == s.len());
    assert(forall|n: int| 0 <= n < s.len() ==> s[n] == p[n] || p[n] == '?');
    true
}
// </vc-code>

fn main() {
}

}