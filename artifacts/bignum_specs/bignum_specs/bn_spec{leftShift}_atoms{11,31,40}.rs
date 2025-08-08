use vstd::prelude::*;

verus! {

// ATOM BN_11
spec fn valid_bit_string(s: Seq<char>) -> bool {
    forall|i: int| 0 <= i < s.len() ==> (s[i] == '0' || s[i] == '1')
}

// ATOM BN_31
spec fn pow2(n: nat) -> nat
    decreases n
{
    if n == 0 { 1nat } else { 2nat * pow2((n - 1) as nat) }
}

// ATOM BN_40
spec fn str2int(s: Seq<char>) -> nat
    decreases s.len()
{
    if s.len() == 0 { 
        0nat 
    } else { 
        2nat * str2int(s.subrange(0, s.len() - 1)) + 
        (if s[s.len() - 1] == '1' { 1nat } else { 0nat })
    }
}

// SPEC leftShift
fn left_shift(s: Seq<char>, n: nat) -> (res: Seq<char>)
    requires 
        valid_bit_string(s),
    ensures 
        valid_bit_string(res),
        str2int(res) == str2int(s) * pow2(n),
{
    assume(false);
    s
}

}

fn main() {}