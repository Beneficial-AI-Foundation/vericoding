use vstd::prelude::*;

verus! {

// <vc-helpers>
proof fn lemma_match_strings_recursive(s: Seq<char>, p: Seq<char>, i: int)
    requires 
        s.len() == p.len(),
        0 <= i <= s.len(),
        forall|n: int| 0 <= n < i ==> s[n] == p[n] || p[n] == '?'
    ensures 
        (forall|n: int| 0 <= n < s.len() ==> s[n] == p[n] || p[n] == '?') == 
        (i == s.len() || (s[i] == p[i] || p[i] == '?') && forall|n: int| i < n < s.len() ==> s[n] == p[n] || p[n] == '?')
{
    if i == s.len() {
        assert forall|n: int| 0 <= n < s.len() ==> s[n] == p[n] || p[n] == '?' by {
            assert(forall|n: int| 0 <= n < i ==> s[n] == p[n] || p[n] == '?');
            assert(i == s.len());
        }
    } else {
        assert forall|n: int| 0 <= n < s.len() ==> s[n] == p[n] || p[n] == '?' <==> 
               (s[i] == p[i] || p[i] == '?') && forall|n: int| i < n < s.len() ==> s[n] == p[n] || p[n] == '?' by {
            if forall|n: int| 0 <= n < s.len() ==> s[n] == p[n] || p[n] == '?' {
                assert(s[i] == p[i] || p[i] == '?');
                assert(forall|n: int| i < n < s.len() ==> s[n] == p[n] || p[n] == '?');
            }
            if (s[i] == p[i] || p[i] == '?') && forall|n: int| i < n < s.len() ==> s[n] == p[n] || p[n] == '?' {
                assert forall|n: int| 0 <= n < s.len() ==> s[n] == p[n] || p[n] == '?' by {
                    assert(forall|n: int| 0 <= n < i ==> s[n] == p[n] || p[n] == '?');
                    assert(s[i] == p[i] || p[i] == '?');
                    assert(forall|n: int| i < n < s.len() ==> s[n] == p[n] || p[n] == '?');
                }
            }
        }
    }
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
fn match_strings(s: Seq<char>, p: Seq<char>) -> (b: bool)
  requires s.len() == p.len()
  ensures b == (forall|n: int| 0 <= n < s.len() ==> s[n] == p[n] || p[n] == '?')
// </vc-spec>
// </vc-spec>

// <vc-code>
{
    let mut i: usize = 0;
    while i < s.len()
        invariant 
            s.len() == p.len(),
            i <= s.len(),
            forall|n: int| 0 <= n < i ==> s[n] == p[n] || p[n] == '?'
    {
        if s@[i] != p@[i] && p@[i] != '?' {
            proof {
                lemma_match_strings_recursive(s, p, i as int);
            }
            return false;
        }
        i = i + 1;
    }
    proof {
        lemma_match_strings_recursive(s, p, i as int);
    }
    true
}
// </vc-code>

fn main() {
}

}