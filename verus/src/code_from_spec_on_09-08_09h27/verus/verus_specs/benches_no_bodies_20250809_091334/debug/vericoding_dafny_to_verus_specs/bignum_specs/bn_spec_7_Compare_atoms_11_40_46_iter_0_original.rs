use vstd::prelude::*;

verus! {

// ATOMS
// BN_11
spec fn valid_bit_string(s: Seq<char>) -> bool {
    forall|i: int| 0 <= i < s.len() ==> (s[i] == '0' || s[i] == '1')
}

// ATOM BN_46 
spec fn exp_int(x: nat, y: nat) -> nat
    decreases y
{
    if y == 0 { 1nat } else { x * exp_int(x, (y - 1) as nat) }
}

// ATOM BN_40
spec fn str2int(s: Seq<char>) -> nat
    decreases s.len()
{
    if s.len() == 0 {
        0nat
    } else {
        if valid_bit_string(s) {
            2nat * str2int(s.subrange(0, s.len() - 1)) + (if s[s.len() - 1] == '1' { 1nat } else { 0nat })
        } else {
            arbitrary() // arbitrary value if precondition not met
        }
    }
}

// SPEC BN_7
fn compare(s1: Seq<char>, s2: Seq<char>) -> (res: i32)
    requires 
        valid_bit_string(s1) && valid_bit_string(s2)
    ensures
        str2int(s1) < str2int(s2) ==> res == -1,
        str2int(s1) == str2int(s2) ==> res == 0,
        str2int(s1) > str2int(s2) ==> res == 1,
{
    return 0;  // TODO: Remove this line and implement the function body
}

}

fn main() {}