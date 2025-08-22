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
    if i == s.len() - 1 {
        // Base case: splitting at the last position
        assert(s.subrange(0, i + 1) == s);
        assert(s.subrange(i + 1, s.len() as int).len() == 0);
        assert(str2int(s.subrange(i + 1, s.len() as int)) == 0);
        assert(exp_int(2nat, 0nat) == 1nat);
    } else {
        // Recursive case: i < s.len() - 1
        let s_prefix = s.subrange(0, s.len() - 1);
        assert(valid_bit_string(s_prefix));
        
        // Apply inductive hypothesis on the prefix
        str2int_lemma(s_prefix, i);
        
        // Use the recursive definition of str2int
        assert(str2int(s) == 2nat * str2int(s_prefix) + 
               (if s[s.len() - 1] == '1' { 1nat } else { 0nat }));
        
        // The key insight: subranges of s relate to subranges of s_prefix
        assert(s.subrange(0, i + 1) == s_prefix.subrange(0, i + 1));
        assert(s.subrange(i + 1, s.len() as int) == 
               s_prefix.subrange(i + 1, s_prefix.len() as int).push(s[s.len() - 1]));
        
        // Apply the recursive structure
        assert(str2int(s.subrange(i + 1, s.len() as int)) == 
               2nat * str2int(s_prefix.subrange(i + 1, s_prefix.len() as int)) + 
               (if s[s.len() - 1] == '1' { 1nat } else { 0nat }));
        
        // Use properties of exponentiation
        assert(exp_int(2nat, (s.len() - 1 - i) as nat) == 
               2nat * exp_int(2nat, (s_prefix.len() - 1 - i) as nat));
    }
}

}

fn main() {}