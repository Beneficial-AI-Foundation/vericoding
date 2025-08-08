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
    /* code modified by LLM (iteration 1): added decreases clause for termination */
    decreases s.len()
{
    if i == s.len() - 1 {
        // Base case: when i is the last index
        assert(s.subrange(0, i + 1) == s);
        assert(s.subrange(i + 1, s.len() as int).len() == 0);
        assert(str2int(s.subrange(i + 1, s.len() as int)) == 0nat);
        assert(exp_int(2nat, 0nat) == 1nat);
    } else {
        // Recursive case: prove by induction on the suffix
        let right_part = s.subrange(i + 1, s.len() as int);
        assert(right_part.len() > 0);
        
        // Apply the recursive definition of str2int on the full string
        assert(str2int(s) == 2nat * str2int(s.subrange(0, s.len() - 1)) + 
               (if s[s.len() - 1] == '1' { 1nat } else { 0nat }));
        
        // Apply induction hypothesis on the prefix (without the last character)
        if s.len() > 1 {
            str2int_lemma(s.subrange(0, s.len() - 1), i);
        }
        
        // Use properties of exponentiation and the recursive structure
        assert(exp_int(2nat, (s.len() - 1 - i) as nat) == 2nat * exp_int(2nat, (s.len() - 2 - i) as nat));
    }
}

}

fn main() {}