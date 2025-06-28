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
        // When mid is 0, left part is empty
        assert(count_char_in_range(s, c, 0, 0) == 0);
        // Show that count_char_in_range(s, c, 0, s.len()) == count_char(s, c)
        count_char_range_equiv(s, c);
    } else if mid >= s.len() {
        // When mid >= len, right part is empty
        assert(count_char_in_range(s, c, mid, s.len() as int) == 0);
        count_char_range_equiv(s, c);
    } else {
        // Recursive case: use structural induction
        let sub_s = s.subrange(1, s.len() as int);
        count_char_additive(sub_s, c, mid - 1);
        
        if s[0] == c {
            assert(count_char(s, c) == 1 + count_char(sub_s, c));
            assert(count_char_in_range(s, c, 0, mid) == 1 + count_char_in_range(sub_s, c, 0, mid - 1));
        } else {
            assert(count_char(s, c) == count_char(sub_s, c));
            assert(count_char_in_range(s, c, 0, mid) == count_char_in_range(sub_s, c, 0, mid - 1));
        }
    }
}

proof fn count_char_range_equiv(s: Seq<u8>, c: u8)
    ensures count_char(s, c) == count_char_in_range(s, c, 0, s.len() as int)
    decreases s.len()
{
    if s.len() == 0 {
        // Base case
    } else {
        count_char_range_equiv(s.subrange(1, s.len() as int), c);
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
        // Each character is exactly one of b, a, or d
        let first_char = s[0];
        assert(first_char == ('b' as u8) || first_char == ('a' as u8) || first_char == ('d' as u8));
    }
}

// Helper lemma for multiset reasoning
proof fn multiset_equal_by_count(s1: Seq<u8>, s2: Seq<u8>)
    requires 
        forall|k: int| 0 <= k < s1.len() ==> s1[k] == ('b' as u8) || s1[k] == ('a' as u8) || s1[k] == ('d' as u8),
        forall|k: int| 0 <= k < s2.len() ==> s2[k] == ('b' as u8) || s2[k] == ('a' as u8) || s2[k] == ('d' as u8),
        count_char(s1, 'b' as u8) == count_char(s2, 'b' as u8),
        count_char(s1, 'a' as u8) == count_char(s2, 'a' as u8),
        count_char(s1, 'd' as u8) == count_char(s2, 'd' as u8)
    ensures multiset(s1) == multiset(s2)
{
    // Since both sequences only contain b, a, d and have equal counts,
    // their multisets must be equal
    assert(multiset(s1).count('b' as u8) == count_char(s1, 'b' as u8));
    assert(multiset(s1).count('a' as u8) == count_char(s1, 'a' as u8));
    assert(multiset(s1).count('d' as u8) == count_char(s1, 'd' as u8));
    assert(multiset(s2).count('b' as u8) == count_char(s2, 'b' as u8));
    assert(multiset(s2).count('a' as u8) == count_char(s2, 'a' as u8));
    assert(multiset(s2).count('d' as u8) == count_char(s2, 'd' as u8));
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
        // Establish that count_char_in_range for full range equals count_char
        count_char_range_equiv(original_a_seq, 'b' as u8);
        count_char_range_equiv(original_a_seq, 'a' as u8);
        count_char_range_equiv(original_a_seq, 'd' as u8);
        
        // Now we have equal counts
        assert(count_char(result@, 'b' as u8) == count_char(original_a_seq, 'b' as u8));
        assert(count_char(result@, 'a' as u8) == count_char(original_a_seq, 'a' as u8));
        assert(count_char(result@, 'd' as u8) == count_char(original_a_seq, 'd' as u8));
        
        // Prove that result only contains b, a, d
        assert(forall|k: int| 0 <= k < result.len() ==> result[k] == ('b' as u8) || result[k] == ('a' as u8) || result[k] == ('d' as u8));
        
        // Use multiset equality lemma
        multiset_equal_by_count(original_a_seq, result@);
        
        // Prove length equality using count totals
        count_char_total(result@);
        count_char_total(original_a_seq);
    }
    
    // Prove sortedbad property
    proof {
        let s = result@;
        
        // All sections are properly ordered: b's, then a's, then d's
        assert(forall|i: int, j: int| 0 <= i < s.len() && 0 <= j < s.len() && s[i] == ('b' as u8) && (s[j] == ('a' as u8) || s[j] == ('d' as u8)) ==> i < j);
        assert(forall|i: int, j: int| 0 <= i < s.len() && 0 <= j < s.len() && s[i] == ('a' as u8) && s[j] == ('b' as u8) ==> i > j);
        assert(forall|i: int, j: int| 0 <= i < s.len() && 0 <= j < s.len() && s[i] == ('a' as u8) && s[j] == ('d' as u8) ==> i < j);
        assert(forall|i: int, j: int| 0 <= i < s.len() && 0 <= j < s.len() && s[j] == ('d' as u8) && (s[i] == ('a' as u8) || s[i] == ('b' as u8)) ==> i < j);
    }
    
    result
}

}