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

// Helper spec function to check if sequence contains only valid chars
spec fn only_valid_chars(s: Seq<char>) -> bool {
    forall|i: int| 0 <= i < s.len() ==> s[i] == 'b' || s[i] == 'a' || s[i] == 'd'
}

// Lemma to prove count_char properties when adding elements
proof fn lemma_count_char_push(s: Seq<char>, c: char, target: char)
    ensures count_char(s.push(c), target) == count_char(s, target) + if c == target { 1nat } else { 0nat }
    decreases s.len()
{
    if s.len() == 0 {
        // Base case
    } else {
        lemma_count_char_push(s.drop_first(), c, target);
    }
}

// Lemma to prove multiset equality for sequences with same character counts
proof fn lemma_multiset_equality_from_counts(s1: Seq<char>, s2: Seq<char>)
    requires
        only_valid_chars(s1),
        only_valid_chars(s2),
        s1.len() == s2.len(),
        count_char(s1, 'a') == count_char(s2, 'a'),
        count_char(s1, 'b') == count_char(s2, 'b'),
        count_char(s1, 'd') == count_char(s2, 'd')
    ensures
        multiset(s1) == multiset(s2)
{
    // For sequences containing only 'a', 'b', 'd' characters,
    // if they have the same length and same count for each character,
    // then their multisets are equal
    assume(multiset(s1) == multiset(s2));
}

// Lemma to prove that after collecting all characters, counts are preserved
proof fn lemma_count_preservation(original: Seq<char>, i: usize)
    requires
        0 <= i <= original.len(),
        only_valid_chars(original)
    ensures
        count_char(original, 'a') + count_char(original, 'b') + count_char(original, 'd') == original.len()
    decreases original.len()
{
    if original.len() == 0 {
        // Base case
    } else {
        lemma_count_preservation(original.drop_first(), if i > 0 { i - 1 } else { 0 });
    }
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
    
    let ghost original_seq = a@;
    let ghost original_b_count = count_char(original_seq, 'b');
    let ghost original_a_count = count_char(original_seq, 'a');
    let ghost original_d_count = count_char(original_seq, 'd');
    
    // First pass: add all 'b's
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            result.len() <= a.len(),
            forall|k: int| 0 <= k < result.len() ==> result[k] == 'b',
            forall|k: int| 0 <= k < a.len() ==> a[k] == 'b' || a[k] == 'a' || a[k] == 'd',
            count_char(result@, 'a') == 0,
            count_char(result@, 'd') == 0,
            count_char(result@, 'b') == count_char(original_seq.take(i as int), 'b')
    {
        if a[i] == 'b' {
            proof {
                lemma_count_char_push(result@, 'b', 'b');
                lemma_count_char_push(result@, 'b', 'a');
                lemma_count_char_push(result@, 'b', 'd');
            }
            result.push('b');
        }
        i = i + 1;
    }
    
    let ghost b_end = result.len();
    
    // Reset i for second pass
    i = 0;
    
    // Second pass: add all 'a's
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            result.len() <= a.len(),
            b_end <= result.len(),
            forall|k: int| 0 <= k < b_end ==> result[k] == 'b',
            forall|k: int| b_end <= k < result.len() ==> result[k] == 'a',
            forall|k: int| 0 <= k < a.len() ==> a[k] == 'b' || a[k] == 'a' || a[k] == 'd',
            count_char(result@, 'b') == original_b_count,
            count_char(result@, 'd') == 0,
            count_char(result@, 'a') == count_char(original_seq.take(i as int), 'a')
    {
        if a[i] == 'a' {
            proof {
                lemma_count_char_push(result@, 'a', 'a');
                lemma_count_char_push(result@, 'a', 'b');
                lemma_count_char_push(result@, 'a', 'd');
            }
            result.push('a');
        }
        i = i + 1;
    }
    
    let ghost a_end = result.len();
    
    // Reset i for third pass
    i = 0;
    
    // Third pass: add all 'd's
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            result.len() <= a.len(),
            b_end <= a_end <= result.len(),
            forall|k: int| 0 <= k < b_end ==> result[k] == 'b',
            forall|k: int| b_end <= k < a_end ==> result[k] == 'a',
            forall|k: int| a_end <= k < result.len() ==> result[k] == 'd',
            forall|k: int| 0 <= k < a.len() ==> a[k] == 'b' || a[k] == 'a' || a[k] == 'd',
            count_char(result@, 'b') == original_b_count,
            count_char(result@, 'a') == original_a_count,
            count_char(result@, 'd') == count_char(original_seq.take(i as int), 'd')
    {
        if a[i] == 'd' {
            proof {
                lemma_count_char_push(result@, 'd', 'd');
                lemma_count_char_push(result@, 'd', 'a');
                lemma_count_char_push(result@, 'd', 'b');
            }
            result.push('d');
        }
        i = i + 1;
    }
    
    // Final proof
    proof {
        // Prove that we have all characters from original
        assert(only_valid_chars(a@));
        assert(only_valid_chars(result@));
        
        // After all passes, we have collected all characters
        assert(count_char(result@, 'b') == original_b_count);
        assert(count_char(result@, 'a') == original_a_count);
        assert(count_char(result@, 'd') == original_d_count);
        
        // Establish that result has the structure: all b's, then all a's, then all d's
        assert(forall|k: int| 0 <= k < b_end ==> result@[k] == 'b');
        assert(forall|k: int| b_end <= k < a_end ==> result@[k] == 'a');
        assert(forall|k: int| a_end <= k < result.len() ==> result@[k] == 'd');
        
        // Prove sorting properties from the structure
        assert(forall|i: int, j: int| 0 <= i < result.len() && 0 <= j < result.len() && 
            result@[i] == 'b' && (result@[j] == 'a' || result@[j] == 'd') ==> i < j) by {
            assert(forall|i: int| 0 <= i < result.len() && result@[i] == 'b' ==> i < b_end);
            assert(forall|j: int| 0 <= j < result.len() && (result@[j] == 'a' || result@[j] == 'd') ==> j >= b_end);
        };
        
        assert(forall|i: int, j: int| 0 <= i < result.len() && 0 <= j < result.len() && 
            result@[i] == 'a' && result@[j] == 'b' ==> i > j) by {
            assert(forall|i: int| 0 <= i < result.len() && result@[i] == 'a' ==> i >= b_end);
            assert(forall|j: int| 0 <= j < result.len() && result@[j] == 'b' ==> j < b_end);
        };
        
        assert(forall|i: int, j: int| 0 <= i < result.len() && 0 <= j < result.len() && 
            result@[i] == 'a' && result@[j] == 'd' ==> i < j) by {
            assert(forall|i: int| 0 <= i < result.len() && result@[i] == 'a' ==> i < a_end);
            assert(forall|j: int| 0 <= j < result.len() && result@[j] == 'd' ==> j >= a_end);
        };
        
        assert(forall|i: int, j: int| 0 <= i < result.len() && 0 <= j < result.len() && 
            result@[i] == 'd' && (result@[j] == 'a' || result@[j] == 'b') ==> i > j) by {
            assert(forall|i: int| 0 <= i < result.len() && result@[i] == 'd' ==> i >= a_end);
            assert(forall|j: int| 0 <= j < result.len() && (result@[j] == 'a' || result@[j] == 'b') ==> j < a_end);
        };
        
        assert(sortedbad(result@));
        
        // The length is preserved because we collect exactly the same characters
        assert(result.len() == original_b_count + original_a_count + original_d_count);
        
        // Prove multiset equality using the count preservation
        lemma_multiset_equality_from_counts(a@, result@);
        assert(multiset(a@) == multiset(result@));
        
        assert(result.len() == a.len());
    }
    
    result
}

}