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
    /* code modified by LLM (iteration 2): added decreases clause to while loop */
    let mut rev = Vec::new();
    let mut i = 0;
    
    while i < s.len()
        invariant
            i <= s.len(),
            rev.len() == i,
            forall|k: int| 0 <= k < i ==> rev[k] as int == s@[s.len() - 1 - k] as int,
        decreases s.len() - i
    {
        rev.push(s[s.len() - 1 - i]);
        i += 1;
    }
    
    rev
}
// </vc-code>


}

fn main() {}