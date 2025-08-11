use vstd::prelude::*;

verus! {

// ATOM BN_11
spec fn valid_bit_string(s: Seq<char>) -> bool {
    forall|i: int| 0 <= i < s.len() ==> (s[i] == '0' || s[i] == '1')
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

// ATOM BN_46  
spec fn exp_int(x: nat, y: nat) -> nat
    decreases y
{
    if y == 0 {
        1nat
    } else {
        x * exp_int(x, (y - 1) as nat)
    }
}

// SPEC BN_41
proof fn str2int_lemma(s: Seq<char>, i: int)
    requires 
        valid_bit_string(s),
        0 <= i <= s.len() - 1,
        s.len() > 0
    ensures 
        str2int(s) == str2int(s.subrange(0, i + 1)) * exp_int(2nat, (s.len() - 1 - i) as nat) + str2int(s.subrange(i + 1, s.len() as int))
{
    assume(false);  // TODO: Remove this line and implement the proof
}

}

fn main() {}