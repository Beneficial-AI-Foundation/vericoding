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
        assert(pow2(0nat) == 1nat);
        assert(str2int(s) == 0nat);
    } else {
        let s_prefix = s.subrange(0, s.len() - 1);
        assert(valid_bit_string(s_prefix));
        bound(s_prefix); // Inductive hypothesis
        
        // Show that pow2(|s|) > str2int(s)
        let last_bit = if s[s.len() - 1] == '1' { 1nat } else { 0nat };
        assert(str2int(s) == 2nat * str2int(s_prefix) + last_bit);
        assert(pow2(s.len()) == 2nat * pow2(s_prefix.len()));
        assert(s_prefix.len() == s.len() - 1);
        
        // From inductive hypothesis: pow2(s_prefix.len()) > str2int(s_prefix)
        // Therefore: 2 * pow2(s_prefix.len()) > 2 * str2int(s_prefix)
        // Since last_bit <= 1, we have:
        // pow2(s.len()) = 2 * pow2(s_prefix.len()) > 2 * str2int(s_prefix) >= 2 * str2int(s_prefix) + last_bit = str2int(s)
        assert(last_bit <= 1nat);
        assert(2nat * pow2(s_prefix.len()) > 2nat * str2int(s_prefix));
        assert(2nat * str2int(s_prefix) + last_bit < 2nat * str2int(s_prefix) + 2nat);
        assert(2nat * str2int(s_prefix) + 2nat == 2nat * (str2int(s_prefix) + 1nat));
        assert(pow2(s_prefix.len()) > str2int(s_prefix));
        assert(pow2(s_prefix.len()) >= str2int(s_prefix) + 1nat);
        assert(2nat * pow2(s_prefix.len()) >= 2nat * (str2int(s_prefix) + 1nat));
        assert(2nat * (str2int(s_prefix) + 1nat) > 2nat * str2int(s_prefix) + last_bit);
    }
}

}

fn main() {}