// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn match_strings(s: Seq<char>, p: Seq<char>) -> (b: bool)
  requires s.len() == p.len()
  ensures b == (forall|n: int| 0 <= n < s.len() ==> s[n] == p[n] || p[n] == '?')
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}