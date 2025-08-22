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
    if s.len() == 0 {
        // Base case: pow2(0) = 1 > 0 = str2int(empty)
        assert(pow2(0nat) == 1nat);
        assert(str2int(s) == 0nat);
    } else {
        // Inductive case
        let prefix = s.subrange(0, s.len() - 1);
        
        // The prefix is also a valid bit string
        assert(valid_bit_string(prefix)) by {
            assert(forall|i: int| 0 <= i < prefix.len() ==> prefix[i] == s[i]);
        }
        
        // Apply inductive hypothesis
        bound(prefix);
        assert(pow2(prefix.len()) > str2int(prefix));
        
        // Now analyze str2int(s)
        let last_bit_value = if s[s.len() - 1] == '1' { 1nat } else { 0nat };
        assert(str2int(s) == 2nat * str2int(prefix) + last_bit_value);
        
        // Since last_bit_value is at most 1
        assert(last_bit_value <= 1nat);
        
        // So str2int(s) <= 2 * str2int(prefix) + 1
        assert(str2int(s) <= 2nat * str2int(prefix) + 1nat);
        
        // From inductive hypothesis: str2int(prefix) < pow2(prefix.len())
        // So: 2 * str2int(prefix) < 2 * pow2(prefix.len())
        assert(2nat * str2int(prefix) < 2nat * pow2(prefix.len()));
        
        // Therefore: str2int(s) <= 2 * str2int(prefix) + 1 < 2 * pow2(prefix.len()) + 1
        assert(str2int(s) < 2nat * pow2(prefix.len()) + 1nat);
        
        // But pow2(s.len()) = pow2(prefix.len() + 1) = 2 * pow2(prefix.len())
        assert(s.len() == prefix.len() + 1);
        assert(pow2(s.len()) == 2nat * pow2(prefix.len()));
        
        // So str2int(s) < 2 * pow2(prefix.len()) + 1 <= 2 * pow2(prefix.len()) = pow2(s.len())
        // We need strict inequality, so we need to show the +1 doesn't matter
        assert(str2int(s) < 2nat * pow2(prefix.len()));
        assert(pow2(s.len()) == 2nat * pow2(prefix.len()));
        assert(str2int(s) < pow2(s.len()));
    }
}

}

fn main() {}