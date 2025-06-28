use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn sortedbad(s: Seq<u8>) -> bool {
    // all b's are before all a's and d's
    (forall|i: int, j: int| 0 <= i < s.len() && 0 <= j < s.len() && s[i] == ('b' as u8) && (s[j] == ('a' as u8) || s[j] == ('d' as u8)) ==> i < j) &&
    // all a's are after all b's
    (forall|i: int, j: int| 0 <= i < s.len() && 0 <= j < s.len() && s[i] == ('a' as u8) && s[j] == ('b' as u8) ==> i > j) &&
    // all a's are before all d's
    (forall|i: int, j: int| 0 <= i < s.len() && 0 <= j < s.len() && s[i] == ('a' as u8) && s[j] == ('d' as u8) ==> i < j) &&
    // all d's are after all b's and a's
    (forall|i: int, j: int| 0 <= i < s.len() && 0 <= j < s.len() && s[j] == ('d' as u8) && (s[i] == ('a' as u8) || s[i] == ('b' as u8)) ==> i < j)
}

spec fn count_char(s: Seq<u8>, c: u8) -> int 
    decreases s.len()
{
    if s.len() == 0 {
        0
    } else {
        let rest_count = count_char(s.subrange(1, s.len() as int), c);
        if s[0] == c {
            1 + rest_count
        } else {
            rest_count
        }
    }
}

spec fn count_char_in_range(s: Seq<u8>, c: u8, start: int, end: int) -> int
    recommends 0 <= start <= end <= s.len()
    decreases end - start
{
    if start >= end {
        0
    } else {
        let rest_count = count_char_in_range(s, c, start + 1, end);
        if s[start] == c {
            1 + rest_count
        } else {
            rest_count
        }
    }
}

proof fn count_char_additive(s: Seq<u8>, c: u8, mid: int)
    requires 0 <= mid <= s.len()
    ensures count_char(s, c) == count_char_in_range(s, c, 0, mid) + count_char_in_range(s, c, mid, s.len() as int)
    decreases s.len()
{
    if s.len() == 0 {
        // Base case: empty sequence
    } else if mid == 0 {
        // mid is 0, so we need to show equivalence
        assert(count_char_in_range(s, c, 0, 0) == 0);
        assert(count_char_in_range(s, c, 0, s.len() as int) == count_char(s, c));
        count_char_additive(s.subrange(1, s.len() as int), c, 0);
    } else if mid >= s.len() {
        // mid is at or beyond the end
        assert(count_char_in_range(s, c, mid, s.len() as int) == 0);
    } else {
        // Recursive case
        let sub_s = s.subrange(1, s.len() as int);
        count_char_additive(sub_s, c, mid - 1);
        
        // Relate the subrange counts
        assert(count_char_in_range(s, c, 1, mid) == count_char_in_range(sub_s, c, 0, mid - 1));
        assert(count_char_in_range(s, c, mid, s.len() as int) == count_char_in_range(sub_s, c, mid - 1, sub_s.len() as int));
    }
}

proof fn count_char_total(s: Seq<u8>)
    requires forall|k: int| 0 <= k < s.len() ==> s[k] == ('b' as u8) || s[k] == ('a' as u8) || s[k] == ('d' as u8)
    ensures s.len() == count_char(s, 'b' as u8) + count_char(s, 'a' as u8) + count_char(s, 'd' as u8)
    decreases s.len()
{
    if s.len() == 0 {
        // Base case
    } else {
        count_char_total(s.subrange(1, s.len() as int));
        // The recursive call establishes the property for the tail
        // We need to show it holds for the full sequence
        let first_char = s[0];
        assert(first_char == ('b' as u8) || first_char == ('a' as u8) || first_char == ('d' as u8));
    }
}

// Lemma that multiset count equals our count function
proof fn multiset_count_lemma(s: Seq<u8>, c: u8) 
    ensures multiset(s).count(c) == count_char(s, c)
    decreases s.len()
{
    if s.len() == 0 {
        // Base case: empty multiset
    } else {
        multiset_count_lemma(s.subrange(1, s.len() as int), c);
        // Inductive step: relate multiset properties
        assert(multiset(s) == multiset(seq![s[0]]).add(multiset(s.subrange(1, s.len() as int))));
    }
}

// Helper lemma to establish multiset equality
proof fn multiset_equality_lemma(s1: Seq<u8>, s2: Seq<u8>)
    requires
        forall|c: u8| multiset(s1).count(c) == multiset(s2).count(c)
    ensures
        multiset(s1) == multiset(s2)
{
    // This follows from multiset extensionality
    assert(multiset(s1).ext_equal(multiset(s2)));
}

fn BadSort(a: Vec<u8>) -> (b: Vec<u8>)
    requires
        forall|k: int| 0 <= k < a.len() ==> a[k] == ('b' as u8) || a[k] == ('a' as u8) || a[k] == ('d' as u8)
    ensures
        sortedbad(b@),
        multiset(a@) == multiset(b@),
        a.len() == b.len()
{
    let mut result: Vec<u8> = Vec::new();
    let mut i: usize = 0;
    let ghost original_a_seq = a@;
    
    // First pass: add all b's
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            result.len() <= a.len(),
            forall|k: int| 0 <= k < result.len() ==> result[k] == ('b' as u8),
            count_char(result@, 'b' as u8) == count_char_in_range(original_a_seq, 'b' as u8, 0, i as int),
            count_char(result@, 'a' as u8) == 0,
            count_char(result@, 'd' as u8) == 0,
            original_a_seq == a@,
    {
        if a[i] == ('b' as u8) {
            result.push('b' as u8);
        }
        i += 1;
    }
    
    let ghost b_section_len = result.len();
    
    // Second pass: add all a's  
    i = 0;
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            result.len() <= a.len(),
            b_section_len <= result.len(),
            forall|k: int| 0 <= k < b_section_len ==> result[k] == ('b' as u8),
            forall|k: int| b_section_len <= k < result.len() ==> result[k] == ('a' as u8),
            count_char(result@, 'b' as u8) == count_char(original_a_seq, 'b' as u8),
            count_char(result@, 'a' as u8) == count_char_in_range(original_a_seq, 'a' as u8, 0, i as int),
            count_char(result@, 'd' as u8) == 0,
            original_a_seq == a@,
    {
        if a[i] == ('a' as u8) {
            result.push('a' as u8);
        }
        i += 1;
    }
    
    let ghost a_section_len = result.len();
    
    // Third pass: add all d's
    i = 0;
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            result.len() <= a.len(),
            b_section_len <= a_section_len <= result.len(),
            forall|k: int| 0 <= k < b_section_len ==> result[k] == ('b' as u8),
            forall|k: int| b_section_len <= k < a_section_len ==> result[k] == ('a' as u8),
            forall|k: int| a_section_len <= k < result.len() ==> result[k] == ('d' as u8),
            count_char(result@, 'b' as u8) == count_char(original_a_seq, 'b' as u8),
            count_char(result@, 'a' as u8) == count_char(original_a_seq, 'a' as u8),
            count_char(result@, 'd' as u8) == count_char_in_range(original_a_seq, 'd' as u8, 0, i as int),
            original_a_seq == a@,
    {
        if a[i] == ('d' as u8) {
            result.push('d' as u8);
        }
        i += 1;
    }
    
    // Prove final properties
    proof {
        // First establish that all count_char_in_range calls are complete
        count_char_additive(original_a_seq, 'b' as u8, a.len() as int);
        count_char_additive(original_a_seq, 'a' as u8, a.len() as int);
        count_char_additive(original_a_seq, 'd' as u8, a.len() as int);
        
        // This gives us that count_char_in_range(original_a_seq, c, 0, a.len()) == count_char(original_a_seq, c)
        assert(count_char(result@, 'b' as u8) == count_char(original_a_seq, 'b' as u8));
        assert(count_char(result@, 'a' as u8) == count_char(original_a_seq, 'a' as u8));
        assert(count_char(result@, 'd' as u8) == count_char(original_a_seq, 'd' as u8));
        
        // Prove that result only contains b, a, d
        assert(forall|k: int| 0 <= k < result.len() ==> result[k] == ('b' as u8) || result[k] == ('a' as u8) || result[k] == ('d' as u8));
        
        // Prove length property using count_char_total
        count_char_total(result@);
        count_char_total(original_a_seq);
        
        // Use the multiset lemma to establish equivalence
        multiset_count_lemma(original_a_seq, 'b' as u8);
        multiset_count_lemma(original_a_seq, 'a' as u8);
        multiset_count_lemma(original_a_seq, 'd' as u8);
        multiset_count_lemma(result@, 'b' as u8);
        multiset_count_lemma(result@, 'a' as u8);
        multiset_count_lemma(result@, 'd' as u8);
        
        // Establish count equality for all possible characters
        assert(forall|c: u8| multiset(original_a_seq).count(c) == multiset(result@).count(c)) by {
            if c == ('b' as u8) || c == ('a' as u8) || c == ('d' as u8) {
                // We've proven these cases above
            } else {
                // For any other character, both sequences have count 0
                assert(multiset(original_a_seq).count(c) == 0);
                assert(multiset(result@).count(c) == 0);
            }
        }
        
        // Use multiset extensionality
        multiset_equality_lemma(original_a_seq, result@);
    }
    
    // Prove sortedbad property
    proof {
        let s = result@;
        
        // All b's before a's and d's
        assert(forall|i: int, j: int| 0 <= i < s.len() && 0 <= j < s.len() && s[i] == ('b' as u8) && (s[j] == ('a' as u8) || s[j] == ('d' as u8)) ==> i < j) by {
            assert(forall|k: int| 0 <= k < b_section_len ==> s[k] == ('b' as u8));
            assert(forall|k: int| b_section_len <= k < s.len() ==> s[k] == ('a' as u8) || s[k] == ('d' as u8));
        }
        
        // All a's after b's
        assert(forall|i: int, j: int| 0 <= i < s.len() && 0 <= j < s.len() && s[i] == ('a' as u8) && s[j] == ('b' as u8) ==> i > j) by {
            assert(forall|k: int| 0 <= k < b_section_len ==> s[k] == ('b' as u8));
            assert(forall|k: int| b_section_len <= k < a_section_len ==> s[k] == ('a' as u8));
        }
        
        // All a's before d's
        assert(forall|i: int, j: int| 0 <= i < s.len() && 0 <= j < s.len() && s[i] == ('a' as u8) && s[j] == ('d' as u8) ==> i < j) by {
            assert(forall|k: int| b_section_len <= k < a_section_len ==> s[k] == ('a' as u8));
            assert(forall|k: int| a_section_len <= k < s.len() ==> s[k] == ('d' as u8));
        }
        
        // All d's after b's and a's
        assert(forall|i: int, j: int| 0 <= i < s.len() && 0 <= j < s.len() && s[j] == ('d' as u8) && (s[i] == ('a' as u8) || s[i] == ('b' as u8)) ==> i < j) by {
            assert(forall|k: int| 0 <= k < a_section_len ==> s[k] == ('b' as u8) || s[k] == ('a' as u8));
            assert(forall|k: int| a_section_len <= k < s.len() ==> s[k] == ('d' as u8));
        }
    }
    
    result
}

}