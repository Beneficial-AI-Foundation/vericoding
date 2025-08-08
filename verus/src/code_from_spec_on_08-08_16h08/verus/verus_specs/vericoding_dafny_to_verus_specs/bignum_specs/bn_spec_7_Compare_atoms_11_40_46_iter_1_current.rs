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
    // Remove leading zeros conceptually by finding first non-zero bit
    let mut start1 = 0;
    let mut start2 = 0;
    
    while start1 < s1.len() && s1[start1] == '0'
        invariant 0 <= start1 <= s1.len()
        invariant forall|i: int| 0 <= i < start1 ==> s1[i] == '0'
    {
        start1 = start1 + 1;
    }
    
    while start2 < s2.len() && s2[start2] == '0'
        invariant 0 <= start2 <= s2.len()
        invariant forall|i: int| 0 <= i < start2 ==> s2[i] == '0'
    {
        start2 = start2 + 1;
    }
    
    let len1 = s1.len() - start1;
    let len2 = s2.len() - start2;
    
    // Compare effective lengths first
    if len1 < len2 {
        return -1;
    } else if len1 > len2 {
        return 1;
    } else {
        // Same effective length, compare bit by bit
        let mut i = start1;
        let mut j = start2;
        
        while i < s1.len()
            invariant start1 <= i <= s1.len()
            invariant j == start2 + (i - start1)
            invariant start2 <= j <= s2.len()
            invariant forall|k: int| start1 <= k < i ==> s1[k] == s2[start2 + (k - start1)]
        {
            if s1[i] < s2[j] {
                return -1;
            } else if s1[i] > s2[j] {
                return 1;
            }
            i = i + 1;
            j = j + 1;
        }
        
        return 0;
    }
}

}

fn main() {}