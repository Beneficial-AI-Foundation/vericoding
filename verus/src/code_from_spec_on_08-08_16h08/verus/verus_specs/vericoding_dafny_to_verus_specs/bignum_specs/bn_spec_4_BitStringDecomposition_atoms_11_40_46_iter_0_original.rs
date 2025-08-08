use vstd::prelude::*;

verus! {

// ATOM BN_11
spec fn valid_bit_string(s: Seq<char>) -> bool {
    // All characters must be '0' or '1'
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
        2nat * str2int(s.subrange(0, s.len() - 1)) + (if s[s.len() - 1] == '1' { 1nat } else { 0nat })
    }
}

// SPEC BN_4
proof fn bit_string_decomposition(s: Seq<char>, i: int) 
    requires 
        valid_bit_string(s),
        i < s.len()
    ensures 
        i >= 0 ==> str2int(s.subrange(0, i + 1)) == str2int(s.subrange(0, i)) * 2nat + (if s[i] == '1' { 1nat } else { 0nat })
{
    if i >= 0 {
        let sub_seq = s.subrange(0, i + 1);
        // sub_seq has length i + 1, and its last element is s[i]
        // By definition of str2int:
        // str2int(sub_seq) = 2 * str2int(sub_seq.subrange(0, sub_seq.len() - 1)) + (if sub_seq[sub_seq.len() - 1] == '1' then 1 else 0)
        // Since sub_seq = s.subrange(0, i + 1), we have:
        // sub_seq.subrange(0, sub_seq.len() - 1) = s.subrange(0, i)
        // sub_seq[sub_seq.len() - 1] = s[i]
        
        assert(sub_seq.len() == i + 1);
        assert(sub_seq.subrange(0, sub_seq.len() - 1) =~= s.subrange(0, i));
        assert(sub_seq[sub_seq.len() - 1] == s[i]);
    }
}

}

fn main() {}