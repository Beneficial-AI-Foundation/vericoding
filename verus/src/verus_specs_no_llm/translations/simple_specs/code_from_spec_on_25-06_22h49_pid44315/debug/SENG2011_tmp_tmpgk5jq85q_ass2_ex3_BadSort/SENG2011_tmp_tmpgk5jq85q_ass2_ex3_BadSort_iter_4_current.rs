use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn sortedbad(s: Seq<u8>) -> bool {
    // all b's are before all a's && d's
    (forall|i: int, j: int| 0 <= i < s.len() && 0 <= j < s.len() && s[i] == ('b' as u8) && (s[j] == ('a' as u8) || s[j] == ('d' as u8)) ==> i < j) &&
    // all a's are after all b's
    (forall|i: int, j: int| 0 <= i < s.len() && 0 <= j < s.len() && s[i] == ('a' as u8) && s[j] == ('b' as u8) ==> i > j) &&
    // all a's are before all d's
    (forall|i: int, j: int| 0 <= i < s.len() && 0 <= j < s.len() && s[i] == ('a' as u8) && s[j] == ('d' as u8) ==> i < j) &&
    // all d's are after all b's && a's
    (forall|i: int, j: int| 0 <= i < s.len() && 0 <= j < s.len() && s[j] == ('d' as u8) && (s[i] == ('a' as u8) || s[i] == ('b' as u8)) ==> i > j)
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
    } else if mid == 0 {
        count_char_additive(s.subrange(1, s.len() as int), c, 0);
    } else {
        count_char_additive(s.subrange(1, s.len() as int), c, mid - 1);
    }
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
        count_char_additive(original_a_seq, 'b' as u8, a.len() as int);
        count_char_additive(original_a_seq, 'a' as u8, a.len() as int);
        count_char_additive(original_a_seq, 'd' as u8, a.len() as int);
        
        assert(count_char(result@, 'b' as u8) == count_char(original_a_seq, 'b' as u8));
        assert(count_char(result@, 'a' as u8) == count_char(original_a_seq, 'a' as u8));
        assert(count_char(result@, 'd' as u8) == count_char(original_a_seq, 'd' as u8));
        
        // Prove length property
        assert(result.len() == count_char(result@, 'b' as u8) + count_char(result@, 'a' as u8) + count_char(result@, 'd' as u8)) by {
            let s = result@;
            assert(forall|k: int| 0 <= k < s.len() ==> s[k] == ('b' as u8) || s[k] == ('a' as u8) || s[k] == ('d' as u8));
        }
        
        assert(a.len() == count_char(original_a_seq, 'b' as u8) + count_char(original_a_seq, 'a' as u8) + count_char(original_a_seq, 'd' as u8)) by {
            assert(forall|k: int| 0 <= k < a.len() ==> a[k] == ('b' as u8) || a[k] == ('a' as u8) || a[k] == ('d' as u8));
        }
    }
    
    // Prove sortedbad property
    proof {
        let s = result@;
        
        assert(forall|i: int, j: int| 0 <= i < s.len() && 0 <= j < s.len() && s[i] == ('b' as u8) && (s[j] == ('a' as u8) || s[j] == ('d' as u8)) ==> i < j) by {
            assert(forall|k: int| 0 <= k < b_section_len ==> s[k] == ('b' as u8));
            assert(forall|k: int| b_section_len <= k < s.len() ==> s[k] == ('a' as u8) || s[k] == ('d' as u8));
        }
        
        assert(forall|i: int, j: int| 0 <= i < s.len() && 0 <= j < s.len() && s[i] == ('a' as u8) && s[j] == ('b' as u8) ==> i > j) by {
            assert(forall|k: int| 0 <= k < b_section_len ==> s[k] == ('b' as u8));
            assert(forall|k: int| b_section_len <= k < a_section_len ==> s[k] == ('a' as u8));
        }
        
        assert(forall|i: int, j: int| 0 <= i < s.len() && 0 <= j < s.len() && s[i] == ('a' as u8) && s[j] == ('d' as u8) ==> i < j) by {
            assert(forall|k: int| b_section_len <= k < a_section_len ==> s[k] == ('a' as u8));
            assert(forall|k: int| a_section_len <= k < s.len() ==> s[k] == ('d' as u8));
        }
        
        assert(forall|i: int, j: int| 0 <= i < s.len() && 0 <= j < s.len() && s[j] == ('d' as u8) && (s[i] == ('a' as u8) || s[i] == ('b' as u8)) ==> i > j) by {
            assert(forall|k: int| 0 <= k < a_section_len ==> s[k] == ('b' as u8) || s[k] == ('a' as u8));
            assert(forall|k: int| a_section_len <= k < s.len() ==> s[k] == ('d' as u8));
        }
    }
    
    result
}

}