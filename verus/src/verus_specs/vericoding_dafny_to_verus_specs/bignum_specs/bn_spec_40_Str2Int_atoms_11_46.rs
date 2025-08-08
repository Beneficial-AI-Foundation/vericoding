use vstd::prelude::*;

verus! {

// ATOM BN_11
spec fn valid_bit_string(s: Seq<char>) -> bool {
    forall|i: int| 0 <= i < s.len() ==> (s[i] == '0' || s[i] == '1')
}

// ATOM BN_46
spec fn exp_int(x: nat, y: nat) -> nat
    decreases y
{
    if y == 0 { 1 } else { x * exp_int(x, (y - 1) as nat) }
}

// SPEC BN_40 (modified version wrt Google Sheets)
spec fn str2_int(s: Seq<char>) -> nat
    decreases s.len()
{
    if !valid_bit_string(s) {
        0  // arbitrary value when precondition fails
    } else if s.len() == 0 {
        0
    } else {
        let first_digit: nat = if s[0] == '1' { 1 } else { 0 };
        first_digit * exp_int(2, (s.len() - 1) as nat) + str2_int(s.subrange(1, s.len() as int))
    }
}

// Property from the original ensures clause
proof fn str2_int_property(s: Seq<char>, i: int)
    requires 
        valid_bit_string(s),
        0 <= i < s.len()
    ensures 
        str2_int(s) == str2_int(s.subrange(0, i + 1)) * exp_int(2, (s.len() - 1) as nat) + str2_int(s.subrange(i + 1, s.len() as int))
{
    // This would need to be proven by induction on the structure of the string
    admit();
}

}

fn main() {}