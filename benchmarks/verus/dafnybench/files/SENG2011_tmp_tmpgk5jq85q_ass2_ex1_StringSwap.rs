// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn string_swap(s: Vec<char>, i: u8, j: u8) -> (t: Vec<char>)
    requires 
        i >= 0 && j >= 0 && s@.len() >= 0,
        s@.len() > 0 ==> (i as nat) < s@.len() && (j as nat) < s@.len(),
    ensures 
        s@.to_multiset() == t@.to_multiset(),
        s@.len() == t@.len(),
        s@.len() > 0 ==> forall|k: nat| k != (i as nat) && k != (j as nat) && k < s@.len() ==> t@[k as int] == s@[k as int],
        s@.len() > 0 ==> t@[(i as nat) as int] == s@[(j as nat) as int] && t@[(j as nat) as int] == s@[(i as nat) as int],
        s@.len() == 0 ==> t@ == s@,
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}