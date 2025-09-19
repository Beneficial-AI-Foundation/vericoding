// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn number_to_name(n: int) -> &'static str
{
    if n == 1 { "One" }
    else if n == 2 { "Two" }
    else if n == 3 { "Three" }
    else if n == 4 { "Four" }
    else if n == 5 { "Five" }
    else if n == 6 { "Six" }
    else if n == 7 { "Seven" }
    else if n == 8 { "Eight" }
    else { "Nine" }
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn reverse(s: Vec<i8>) -> (rev: Vec<i8>)
    ensures 
        rev.len() == s.len(),
        forall|k: int| 0 <= k < s.len() ==> rev[k] as int == s@[s.len() - 1 - k] as int
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>


}

fn main() {}