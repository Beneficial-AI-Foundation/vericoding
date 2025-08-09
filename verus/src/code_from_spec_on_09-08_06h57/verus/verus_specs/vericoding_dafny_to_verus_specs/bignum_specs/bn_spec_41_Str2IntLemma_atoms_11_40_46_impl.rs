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
    decreases s.len()
{
    /* code modified by LLM (iteration 1): added decreases clause and restructured proof with proper induction */
    let left_part = s.subrange(0, i + 1);
    let right_part = s.subrange(i + 1, s.len() as int);
    let power = (s.len() - 1 - i) as nat;
    
    if right_part.len() == 0 {
        // Base case: right part is empty, so i == s.len() - 1
        assert(i + 1 == s.len());
        assert(left_part == s);
        assert(str2int(right_part) == 0);
        assert(power == 0);
        assert(exp_int(2nat, 0) == 1);
        assert(str2int(s) == str2int(left_part) * 1 + 0);
    } else {
        // Inductive case: split based on the structure of str2int
        if s.len() == 1 {
            // Simple case with single bit
            assert(i == 0);
            assert(left_part.len() == 1);
            assert(right_part.len() == 0);
        } else {
            // Use induction on shorter string
            let s_without_last = s.subrange(0, s.len() - 1);
            let last_bit = s[s.len() - 1];
            
            if i < s.len() - 1 {
                // Apply inductive hypothesis on prefix
                str2int_lemma(s_without_last, i);
                
                // Connect the recursive structure
                assert(str2int(s) == 2nat * str2int(s_without_last) + (if last_bit == '1' { 1nat } else { 0nat }));
            } else {
                // Case where i == s.len() - 1
                assert(right_part.len() == 0);
            }
        }
    }
}

}

fn main() {}