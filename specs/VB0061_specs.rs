// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn all_zero(s: Seq<char>) -> bool {
    s.len() == 0 || forall|i: int| 0 <= i < s.len() ==> s[i] == '0'
}

spec fn str2int(s: Seq<char>) -> nat
    decreases s.len()
{
    if s.len() == 0 { 
        0nat 
    } else { 
        2nat * str2int(s.subrange(0, s.len() - 1)) + (if s[s.len() - 1] == '1' { 1nat } else { 0nat })
    }
}

spec fn valid_bit_string(s: Seq<char>) -> bool {
    forall|i: int| 0 <= i < s.len() ==> s[i] == '0' || s[i] == '1'
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn zeros(n: usize) -> (s: Vec<char>)
    ensures 
        s@.len() == n,
        valid_bit_string(s@),
        str2int(s@) == 0,
        all_zero(s@)
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>


}

fn main() {}