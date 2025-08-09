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

// Helper lemma to prove that longer valid bit strings represent larger integers
proof fn lemma_longer_string_larger(s1: Seq<char>, s2: Seq<char>)
    requires
        valid_bit_string(s1),
        valid_bit_string(s2),
        s1.len() > 0,
        s2.len() > 0,
        s1.len() > s2.len()
    ensures
        str2int(s1) >= exp_int(2nat, s2.len() as nat),
        str2int(s2) < exp_int(2nat, s2.len() as nat),
        str2int(s1) > str2int(s2)
    decreases s1.len()
{
    if s1.len() == 1 {
        assert(s2.len() == 0);
        assert(str2int(s2) == 0);
        assert(str2int(s1) >= 1);
    } else {
        let s1_prefix = s1.subrange(0, s1.len() - 1);
        lemma_longer_string_larger(s1_prefix, s2);
        /* code modified by LLM (iteration 1): Fixed type annotations for integer literals */
        assert(str2int(s1) == 2 * str2int(s1_prefix) + (if s1[s1.len() - 1] == '1' { 1nat } else { 0nat }));
        assert(str2int(s1) >= 2 * exp_int(2nat, s2.len() as nat));
        lemma_exp_multiply(2nat, s2.len() as nat);
    }
}

proof fn lemma_exp_multiply(x: nat, y: nat)
    requires x > 0
    ensures 2 * exp_int(x, y) == exp_int(x, y + 1)
    decreases y
{
    if y == 0 {
    } else {
        lemma_exp_multiply(x, (y - 1) as nat);
    }
}

proof fn lemma_string_upper_bound(s: Seq<char>)
    requires valid_bit_string(s), s.len() > 0
    ensures str2int(s) < exp_int(2nat, s.len() as nat)
    decreases s.len()
{
    if s.len() == 1 {
        assert(str2int(s) <= 1);
        assert(exp_int(2nat, 1nat) == 2);
    } else {
        let prefix = s.subrange(0, s.len() - 1);
        lemma_string_upper_bound(prefix);
        /* code modified by LLM (iteration 1): Fixed type annotations for integer literals */
        assert(str2int(s) == 2 * str2int(prefix) + (if s[s.len() - 1] == '1' { 1nat } else { 0nat }));
        assert(str2int(s) <= 2 * str2int(prefix) + 1);
        assert(str2int(s) < 2 * exp_int(2nat, (s.len() - 1) as nat) + 1);
        lemma_exp_multiply(2nat, (s.len() - 1) as nat);
    }
}

// Helper lemma for lexicographic comparison
proof fn lemma_lex_compare(s1: Seq<char>, s2: Seq<char>)
    requires
        valid_bit_string(s1),
        valid_bit_string(s2),
        s1.len() == s2.len(),
        s1.len() > 0,
        s1[0] > s2[0]
    ensures
        str2int(s1) > str2int(s2)
    decreases s1.len()
{
    if s1.len() == 1 {
        assert(s1[0] == '1' && s2[0] == '0');
        assert(str2int(s1) == 1 && str2int(s2) == 0);
    } else {
        /* code modified by LLM (iteration 1): Fixed subrange parameter types */
        let s1_suffix = s1.subrange(1, s1.len() as int);
        let s2_suffix = s2.subrange(1, s2.len() as int);
        assert(str2int(s1) == 2 * str2int(s1_suffix) + (if s1[s1.len() - 1] == '1' { 1nat } else { 0nat }));
        assert(str2int(s2) == 2 * str2int(s2_suffix) + (if s2[s2.len() - 1] == '1' { 1nat } else { 0nat }));
        
        lemma_string_upper_bound(s2_suffix);
        assert(s1[0] == '1' && s2[0] == '0');
        
        // Convert to the recursive form
        assert(str2int(s1) == 2 * str2int(s1.subrange(0, s1.len() - 1)) + (if s1[s1.len() - 1] == '1' { 1nat } else { 0nat }));
        assert(str2int(s2) == 2 * str2int(s2.subrange(0, s2.len() - 1)) + (if s2[s2.len() - 1] == '1' { 1nat } else { 0nat }));
        
        let s1_prefix = s1.subrange(0, s1.len() - 1);
        let s2_prefix = s2.subrange(0, s2.len() - 1);
        
        assert(s1_prefix[0] == '1' && s2_prefix[0] == '0');
        lemma_lex_compare(s1_prefix, s2_prefix);
        assert(str2int(s1_prefix) > str2int(s2_prefix));
        assert(str2int(s1) >= 2 * str2int(s1_prefix));
        assert(str2int(s2) <= 2 * str2int(s2_prefix) + 1);
    }
}

proof fn lemma_lex_compare_rec(s1: Seq<char>, s2: Seq<char>, pos: int)
    requires
        valid_bit_string(s1),
        valid_bit_string(s2),
        s1.len() == s2.len(),
        0 <= pos < s1.len(),
        forall|i: int| 0 <= i < pos ==> s1[i] == s2[i],
        s1[pos] > s2[pos]
    ensures
        str2int(s1) > str2int(s2)
    decreases s1.len() - pos
{
    if pos == 0 {
        lemma_lex_compare(s1, s2);
    } else {
        /* code modified by LLM (iteration 1): Fixed subrange parameter types */
        let s1_suffix = s1.subrange(1, s1.len() as int);
        let s2_suffix = s2.subrange(1, s2.len() as int);
        
        assert(s1[0] == s2[0]);
        assert(forall|i: int| 0 <= i < pos - 1 ==> s1_suffix[i] == s2_suffix[i]);
        assert(s1_suffix[pos - 1] > s2_suffix[pos - 1]);
        
        lemma_lex_compare_rec(s1_suffix, s2_suffix, pos - 1);
        
        assert(str2int(s1) == 2 * str2int(s1.subrange(0, s1.len() - 1)) + (if s1[s1.len() - 1] == '1' { 1nat } else { 0nat }));
        assert(str2int(s2) == 2 * str2int(s2.subrange(0, s2.len() - 1)) + (if s2[s2.len() - 1] == '1' { 1nat } else { 0nat }));
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
    // Handle empty strings
    /* code modified by LLM (iteration 1): Fixed comparison with nat types - removed nat suffix */
    if s1.len() == 0 && s2.len() == 0 {
        return 0;
    }
    if s1.len() == 0 {
        return -1;
    }
    if s2.len() == 0 {
        return 1;
    }
    
    // Compare lengths first
    if s1.len() < s2.len() {
        proof {
            lemma_longer_string_larger(s2, s1);
        }
        return -1;
    }
    if s1.len() > s2.len() {
        proof {
            lemma_longer_string_larger(s1, s2);
        }
        return 1;
    }
    
    // Same length, compare lexicographically
    /* code modified by LLM (iteration 2): Fixed variable type to usize and loop operations */
    let mut i: usize = 0;
    while i < s1.len()
        invariant
            0 <= i <= s1.len(),
            s1.len() == s2.len(),
            valid_bit_string(s1),
            valid_bit_string(s2),
            forall|j: int| 0 <= j < i ==> s1[j] == s2[j]
    {
        /* code modified by LLM (iteration 3): Fixed sequence indexing to use usize directly without int cast */
        if s1[i as int] < s2[i as int] {
            proof {
                assert(s1[i as int] == '0' && s2[i as int] == '1');
                lemma_lex_compare_rec(s2, s1, i as int);
            }
            return -1;
        }
        if s1[i as int] > s2[i as int] {
            proof {
                assert(s1[i as int] == '1' && s2[i as int] == '0');
                lemma_lex_compare_rec(s1, s2, i as int);
            }
            return 1;
        }
        i = i + 1;
    }
    
    // All characters are equal
    proof {
        assert(forall|j: int| 0 <= j < s1.len() ==> s1[j] == s2[j]);
        assert(s1 =~= s2);
    }
    return 0;
}

}

fn main() {}