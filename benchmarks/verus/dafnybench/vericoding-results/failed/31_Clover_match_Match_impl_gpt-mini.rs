use vstd::prelude::*;

verus! {

// <vc-helpers>
fn prefix_match(s: Seq<char>, p: Seq<char>, i: nat) -> bool
  requires s.len() == p.len()
  requires i <= s.len()
  ensures result == (forall |m: int| 0 <= m && m < (i as int) ==> (s@[m as nat] == p@[m as nat] || p@[m as nat] == '?'))
  decreases i
{
    if i == 0 {
        true
    } else {
        let i1: nat = i - 1;
        let prev: bool = prefix_match(s, p, i1);
        let cond: bool = s@[i1] == p@[i1] || p@[i1] == '?';
        prev && cond
    }
}
// </vc-helpers>

// <vc-spec>
fn match_strings(s: Seq<char>, p: Seq<char>) -> (b: bool)
  requires s.len() == p.len()
  ensures b == (forall|n: int| 0 <= n < s.len() ==> s[n] == p[n] || p[n] == '?')
// </vc-spec>
// <vc-code>
{
    prefix_match(s, p, s.len())
}
// </vc-code>

fn main() {
}

}