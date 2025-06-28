use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn sortedbad(s: String) -> bool {
    // all b's are before all a's && d's
    (forall|i: int, j: int| 0 <= i < s.len() && 0 <= j < s.len() && s.spec_index(i) == 'b' && (s.spec_index(j) == 'a' || s.spec_index(j) == 'd') ==> i < j) &&
    // all a's are after all b's
    (forall|i: int, j: int| 0 <= i < s.len() && 0 <= j < s.len() && s.spec_index(i) == 'a' && s.spec_index(j) == 'b' ==> i > j) &&
    // all a's are before all d's
    (forall|i: int, j: int| 0 <= i < s.len() && 0 <= j < s.len() && s.spec_index(i) == 'a' && s.spec_index(j) == 'd' ==> i < j) &&
    // all d's are after all b's && a's
    (forall|i: int, j: int| 0 <= i < s.len() && 0 <= j < s.len() && s.spec_index(i) == 'd' && (s.spec_index(j) == 'a' || s.spec_index(j) == 'b') ==> i > j)
}

spec fn count_char(s: Seq<char>, c: char) -> int 
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

fn BadSort(a: String) -> (b: String)
    requires
        forall|k: int| 0 <= k < a.len() ==> a.spec_index(k) == 'b' || a.spec_index(k) == 'a' || a.spec_index(k) == 'd'
    ensures
        sortedbad(b),
        multiset(a.spec_index(..)) == multiset(b.spec_index(..)),
        a.len() == b.len()
{
    let mut result = String::new();
    let mut i: usize = 0;
    let ghost original_a_seq = a.spec_index(..);
    
    // Count characters for invariants
    let ghost b_count = count_char(original_a_seq, 'b');
    let ghost a_count = count_char(original_a_seq, 'a');  
    let ghost d_count = count_char(original_a_seq, 'd');
    
    // First pass: add all b's
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            result.len() <= a.len(),
            forall|k: int| 0 <= k < result.len() ==> result.spec_index(k) == 'b',
            count_char(result.spec_index(..), 'b') == count_char(original_a_seq.subrange(0, i as int), 'b'),
            original_a_seq == a.spec_index(..),
    {
        if a.as_bytes()[i] == b'b' {
            result.push('b');
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
            forall|k: int| 0 <= k < b_section_len ==> result.spec_index(k) == 'b',
            forall|k: int| b_section_len <= k < result.len() ==> result.spec_index(k) == 'a',
            count_char(result.spec_index(..), 'b') == count_char(original_a_seq, 'b'),
            count_char(result.spec_index(..), 'a') == count_char(original_a_seq.subrange(0, i as int), 'a'),
            original_a_seq == a.spec_index(..),
    {
        if a.as_bytes()[i] == b'a' {
            result.push('a');
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
            forall|k: int| 0 <= k < b_section_len ==> result.spec_index(k) == 'b',
            forall|k: int| b_section_len <= k < a_section_len ==> result.spec_index(k) == 'a',
            forall|k: int| a_section_len <= k < result.len() ==> result.spec_index(k) == 'd',
            count_char(result.spec_index(..), 'b') == count_char(original_a_seq, 'b'),
            count_char(result.spec_index(..), 'a') == count_char(original_a_seq, 'a'),
            count_char(result.spec_index(..), 'd') == count_char(original_a_seq.subrange(0, i as int), 'd'),
            original_a_seq == a.spec_index(..),
    {
        if a.as_bytes()[i] == b'd' {
            result.push('d');
        }
        i += 1;
    }
    
    // Prove final properties
    assert(count_char(result.spec_index(..), 'b') == count_char(original_a_seq, 'b'));
    assert(count_char(result.spec_index(..), 'a') == count_char(original_a_seq, 'a'));
    assert(count_char(result.spec_index(..), 'd') == count_char(original_a_seq, 'd'));
    
    // Prove length property
    proof {
        assert(result.len() == count_char(result.spec_index(..), 'b') + count_char(result.spec_index(..), 'a') + count_char(result.spec_index(..), 'd'));
        assert(a.len() == count_char(original_a_seq, 'b') + count_char(original_a_seq, 'a') + count_char(original_a_seq, 'd')) by {
            assert(forall|k: int| 0 <= k < a.len() ==> a.spec_index(k) == 'b' || a.spec_index(k) == 'a' || a.spec_index(k) == 'd');
        }
    }
    
    // Prove sortedbad property
    proof {
        assert(forall|i: int, j: int| 0 <= i < result.len() && 0 <= j < result.len() && result.spec_index(i) == 'b' && (result.spec_index(j) == 'a' || result.spec_index(j) == 'd') ==> i < j) by {
            assert(forall|k: int| 0 <= k < b_section_len ==> result.spec_index(k) == 'b');
            assert(forall|k: int| b_section_len <= k < result.len() ==> result.spec_index(k) == 'a' || result.spec_index(k) == 'd');
        }
        
        assert(forall|i: int, j: int| 0 <= i < result.len() && 0 <= j < result.len() && result.spec_index(i) == 'a' && result.spec_index(j) == 'b' ==> i > j) by {
            assert(forall|k: int| 0 <= k < b_section_len ==> result.spec_index(k) == 'b');
            assert(forall|k: int| b_section_len <= k < a_section_len ==> result.spec_index(k) == 'a');
        }
        
        assert(forall|i: int, j: int| 0 <= i < result.len() && 0 <= j < result.len() && result.spec_index(i) == 'a' && result.spec_index(j) == 'd' ==> i < j) by {
            assert(forall|k: int| b_section_len <= k < a_section_len ==> result.spec_index(k) == 'a');
            assert(forall|k: int| a_section_len <= k < result.len() ==> result.spec_index(k) == 'd');
        }
        
        assert(forall|i: int, j: int| 0 <= i < result.len() && 0 <= j < result.len() && result.spec_index(i) == 'd' && (result.spec_index(j) == 'a' || result.spec_index(j) == 'b') ==> i > j) by {
            assert(forall|k: int| 0 <= k < a_section_len ==> result.spec_index(k) == 'b' || result.spec_index(k) == 'a');
            assert(forall|k: int| a_section_len <= k < result.len() ==> result.spec_index(k) == 'd');
        }
    }
    
    // Prove multiset equality
    proof {
        assert(multiset(original_a_seq) == multiset(result.spec_index(..))) by {
            assert(count_char(result.spec_index(..), 'b') == count_char(original_a_seq, 'b'));
            assert(count_char(result.spec_index(..), 'a') == count_char(original_a_seq, 'a'));
            assert(count_char(result.spec_index(..), 'd') == count_char(original_a_seq, 'd'));
            assert(forall|c: char| c != 'a' && c != 'b' && c != 'd' ==> count_char(original_a_seq, c) == 0);
            assert(forall|c: char| c != 'a' && c != 'b' && c != 'd' ==> count_char(result.spec_index(..), c) == 0);
        }
    }
    
    result
}

}