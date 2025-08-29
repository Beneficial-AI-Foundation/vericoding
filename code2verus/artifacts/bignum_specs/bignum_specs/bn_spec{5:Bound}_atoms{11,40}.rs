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
        2nat * str2int(s.subrange(0, s.len() - 1)) + (if s[s.len() - 1] == '1' { 1nat } else { 0nat })
    }
}

// SPEC BN_5
proof fn bound(s: Seq<char>)
    requires valid_bit_string(s)
    ensures pow2(s.len()) > str2int(s)
    decreases s.len()
{
    // Proof by induction on length of s
    if s.len() == 0 {
        // Base case: pow2(0) = 1 > 0 = str2int("")
    } else {
        let s_prefix = s.subrange(0, s.len() - 1);
        assert(valid_bit_string(s_prefix));
        bound(s_prefix); // Inductive hypothesis
        
        // Show that pow2(|s|) > str2int(s)
        // pow2(|s|) = 2 * pow2(|s|-1) > 2 * str2int(s_prefix) >= 2 * str2int(s_prefix) + bit
        // where bit is 0 or 1, so pow2(|s|) > str2int(s)
    }
}

}

fn main() {}