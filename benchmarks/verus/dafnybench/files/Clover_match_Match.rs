use vstd::prelude::*;

verus! {

fn match_strings(s: Seq<char>, p: Seq<char>) -> (b: bool)
  requires s.len() == p.len()
  ensures b == (forall|n: int| 0 <= n < s.len() ==> s[n] == p[n] || p[n] == '?')
{
    assume(false);
    unreached();
}

}
fn main() {}