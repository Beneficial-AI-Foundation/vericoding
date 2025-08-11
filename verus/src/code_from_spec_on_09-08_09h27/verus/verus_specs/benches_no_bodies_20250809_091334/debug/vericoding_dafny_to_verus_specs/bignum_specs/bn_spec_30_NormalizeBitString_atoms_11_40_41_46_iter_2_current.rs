use vstd::prelude::*;

verus! {

// ATOM
// BN_46
pub open spec fn valid_bit_string(s: Seq<char>) -> bool {
    forall|i: int| 0 <= i < s.len() ==> s[i] == '0' || s[i] == '1'
}

// ATOM
//BN_11
pub open spec fn exp_int(x: nat, y: nat) -> nat 
    decreases y
{
    if y == 0 { 1nat } else { x * exp_int(x, (y - 1) as nat) }
}

// ATOM
// BN_40
pub open spec fn str2int(s: Seq<char>) -> nat 
    recommends valid_bit_string(s)
    decreases s.len()
{
    if s.len() == 0 { 
        0nat 
    } else { 
        2nat * str2int(s.subrange(0, (s.len() - 1) as int)) + (if s[(s.len() - 1) as int] == '1' { 1nat } else { 0nat })
    }
}

// ATOM BN_41
proof fn str2int_lemma(s: Seq<char>, i: nat)
    requires valid_bit_string(s),
             0 <= i <= s.len() - 1,
    ensures str2int(s) == str2int(s.subrange(0, (i + 1) as int)) * exp_int(2nat, (s.len() - 1 - i) as nat) + str2int(s.subrange((i + 1) as int, s.len() as int))
{
    let left = s.subrange(0, (i + 1) as int);
    let right = s.subrange((i + 1) as int, s.len() as int);
    let power = exp_int(2nat, (s.len() - 1 - i) as nat);
    
    if i + 1 == s.len() {
        // Base case: right part is empty
        assert(right.len() == 0);
        assert(str2int(right) == 0);
        assert(left == s);
        assert(power == 1);
    } else {
        // Inductive case
        str2int_lemma(s, i + 1);
    }
}

/* code modified by LLM (iteration 1): converted imperative loop to recursive helper function for spec function */
spec fn find_first_one_index(s: Seq<char>, start: int) -> int
    decreases s.len() - start
{
    if start >= s.len() {
        s.len() as int
    } else if s[start] == '1' {
        start
    } else {
        find_first_one_index(s, start + 1)
    }
}

// SPEC BN_30
/* code modified by LLM (iteration 1): replaced imperative loop with recursive helper function call */
spec fn normalize_bit_string(s: Seq<char>) -> Seq<char>
{
    if s.len() == 0 {
        seq!['0']
    } else if s[0] == '1' {
        s
    } else {
        // Remove leading zeros
        let first_one = find_first_one_index(s, 0);
        if first_one == s.len() {
            seq!['0']  // All zeros case
        } else {
            s.subrange(first_one, s.len() as int)
        }
    }
}

}

fn main() {}