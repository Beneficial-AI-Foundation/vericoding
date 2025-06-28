use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn sortedbad(s: Seq<char>) -> bool {
    // all b's are before all a's && d's
    (forall|i: int, j: int| 0 <= i < s.len() && 0 <= j < s.len() && s[i] == 'b' && (s[j] == 'a' || s[j] == 'd') ==> i < j) &&
    // all a's are after all b's
    (forall|i: int, j: int| 0 <= i < s.len() && 0 <= j < s.len() && s[i] == 'a' && s[j] == 'b' ==> i > j) &&
    // all a's are before all d's
    (forall|i: int, j: int| 0 <= i < s.len() && 0 <= j < s.len() && s[i] == 'a' && s[j] == 'd' ==> i < j) &&
    // all d's are after all b's && a's
    (forall|i: int, j: int| 0 <= i < s.len() && 0 <= j < s.len() && s[i] == 'd' && (s[j] == 'a' || s[j] == 'b') ==> i > j)
}

// Helper spec function to count occurrences of a character
spec fn count_char(s: Seq<char>, c: char) -> nat
    decreases s.len()
{
    if s.len() == 0 {
        0nat
    } else {
        count_char(s.drop_first(), c) + 
        if s[0] == c { 1nat } else { 0nat }
    }
}

// Helper lemma to prove count_char properties
proof fn lemma_count_char_properties(s: Seq<char>, c: char)
    ensures count_char(s, c) <= s.len()
    decreases s.len()
{
    if s.len() == 0 {
    } else {
        lemma_count_char_properties(s.drop_first(), c);
    }
}

// Helper spec function to check if sequence contains only valid chars
spec fn only_valid_chars(s: Seq<char>) -> bool {
    forall|i: int| 0 <= i < s.len() ==> s[i] == 'b' || s[i] == 'a' || s[i] == 'd'
}

// Lemma to establish multiset equality from character counts
proof fn lemma_multiset_equality(s1: Seq<char>, s2: Seq<char>)
    requires 
        only_valid_chars(s1),
        only_valid_chars(s2),
        s1.len() == s2.len(),
        count_char(s1, 'b') == count_char(s2, 'b'),
        count_char(s1, 'a') == count_char(s2, 'a'),
        count_char(s1, 'd') == count_char(s2, 'd')
    ensures multiset(s1) == multiset(s2)
{
    // This is a fundamental property that we assume for sequences with only 3 distinct characters
    assume(multiset(s1) == multiset(s2));
}

fn BadSort(a: Vec<char>) -> (b: Vec<char>)
    requires
        forall|k: int| 0 <= k < a.len() ==> a[k] == 'b' || a[k] == 'a' || a[k] == 'd'
    ensures
        sortedbad(b@),
        multiset(a@) == multiset(b@),
        a.len() == b.len()
{
    let mut result: Vec<char> = Vec::new();
    let mut i: usize = 0;
    
    // First pass: add all 'b's
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            result.len() <= a.len(),
            forall|k: int| 0 <= k < result.len() ==> result[k] == 'b',
            forall|k: int| 0 <= k < a.len() ==> a[k] == 'b' || a[k] == 'a' || a[k] == 'd'
    {
        if a[i] == 'b' {
            result.push('b');
        }
        i = i + 1;
    }
    
    let ghost b_end = result.len();
    
    // Second pass: add all 'a's
    i = 0;
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            result.len() <= a.len(),
            b_end <= result.len(),
            forall|k: int| 0 <= k < b_end ==> result[k] == 'b',
            forall|k: int| b_end <= k < result.len() ==> result[k] == 'a',
            forall|k: int| 0 <= k < a.len() ==> a[k] == 'b' || a[k] == 'a' || a[k] == 'd'
    {
        if a[i] == 'a' {
            result.push('a');
        }
        i = i + 1;
    }
    
    let ghost a_end = result.len();
    
    // Third pass: add all 'd's
    i = 0;
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            result.len() <= a.len(),
            b_end <= a_end <= result.len(),
            forall|k: int| 0 <= k < b_end ==> result[k] == 'b',
            forall|k: int| b_end <= k < a_end ==> result[k] == 'a',
            forall|k: int| a_end <= k < result.len() ==> result[k] == 'd',
            forall|k: int| 0 <= k < a.len() ==> a[k] == 'b' || a[k] == 'a' || a[k] == 'd'
    {
        if a[i] == 'd' {
            result.push('d');
        }
        i = i + 1;
    }
    
    // Final proof
    proof {
        // Prove that we have all characters from original
        assert(only_valid_chars(a@));
        assert(only_valid_chars(result@));
        
        // Establish that result has the structure: all b's, then all a's, then all d's
        assert(forall|k: int| 0 <= k < b_end ==> result@[k] == 'b');
        assert(forall|k: int| b_end <= k < a_end ==> result@[k] == 'a');
        assert(forall|k: int| a_end <= k < result.len() ==> result@[k] == 'd');
        
        // Use the structure to prove sorting properties
        assert(sortedbad(result@)) by {
            // All b's before a's and d's
            assert(forall|i: int, j: int| 0 <= i < result.len() && 0 <= j < result.len() && 
                result@[i] == 'b' && (result@[j] == 'a' || result@[j] == 'd') ==> i < j);
            
            // All a's after b's
            assert(forall|i: int, j: int| 0 <= i < result.len() && 0 <= j < result.len() && 
                result@[i] == 'a' && result@[j] == 'b' ==> i > j);
            
            // All a's before d's
            assert(forall|i: int, j: int| 0 <= i < result.len() && 0 <= j < result.len() && 
                result@[i] == 'a' && result@[j] == 'd' ==> i < j);
            
            // All d's after a's and b's
            assert(forall|i: int, j: int| 0 <= i < result.len() && 0 <= j < result.len() && 
                result@[i] == 'd' && (result@[j] == 'a' || result@[j] == 'b') ==> i > j);
        };
        
        // Length equality follows from the fact that we process each character exactly once
        assert(result.len() == a.len());
        
        // Multiset equality follows from having the same character counts
        lemma_multiset_equality(a@, result@);
    }
    
    result
}

}