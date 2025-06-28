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

spec fn count_char(s: String, c: char) -> int {
    s.spec_index(..).count(c)
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
    let mut i = 0;
    let ghost original_a = a;
    
    // Count characters for invariants
    let ghost b_count = count_char(a, 'b');
    let ghost a_count = count_char(a, 'a');  
    let ghost d_count = count_char(a, 'd');
    
    // First pass: add all b's
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            result.len() <= a.len(),
            forall|k: int| 0 <= k < result.len() ==> result.spec_index(k) == 'b',
            count_char(result, 'b') == count_char(a.spec_index(..i), 'b'),
            a == original_a,
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
            forall|k: int| 0 <= k < b_section_len ==> result.spec_index(k) == 'b',
            forall|k: int| b_section_len <= k < result.len() ==> result.spec_index(k) == 'a',
            count_char(result, 'b') == count_char(a, 'b'),
            count_char(result, 'a') == count_char(a.spec_index(..i), 'a'),
            a == original_a,
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
            forall|k: int| 0 <= k < b_section_len ==> result.spec_index(k) == 'b',
            forall|k: int| b_section_len <= k < a_section_len ==> result.spec_index(k) == 'a',
            forall|k: int| a_section_len <= k < result.len() ==> result.spec_index(k) == 'd',
            count_char(result, 'b') == count_char(a, 'b'),
            count_char(result, 'a') == count_char(a, 'a'),
            count_char(result, 'd') == count_char(a.spec_index(..i), 'd'),
            a == original_a,
    {
        if a.as_bytes()[i] == b'd' {
            result.push('d');
        }
        i += 1;
    }
    
    // Prove final properties
    assert(count_char(result, 'b') == count_char(a, 'b'));
    assert(count_char(result, 'a') == count_char(a, 'a'));
    assert(count_char(result, 'd') == count_char(a, 'd'));
    
    // Prove sortedbad property
    assert(forall|k: int| 0 <= k < b_section_len ==> result.spec_index(k) == 'b');
    assert(forall|k: int| b_section_len <= k < a_section_len ==> result.spec_index(k) == 'a');
    assert(forall|k: int| a_section_len <= k < result.len() ==> result.spec_index(k) == 'd');
    
    // Length property
    assert(result.len() == b_count + a_count + d_count);
    assert(a.len() == b_count + a_count + d_count);
    
    result
}

}