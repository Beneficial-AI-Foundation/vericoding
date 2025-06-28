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

// Helper spec function to count occurrences of a character
spec fn count_char(s: String, c: char) -> int
    decreases s.len()
{
    if s.len() == 0 {
        0
    } else {
        count_char(s.spec_index(1..s.len()), c) + 
        if s.spec_index(0) == c { 1 } else { 0 }
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
    let mut i = 0;
    
    // First pass: add all 'b's
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            result.len() <= a.len(),
            forall|k: int| 0 <= k < result.len() ==> result.spec_index(k) == 'b',
            forall|k: int| 0 <= k < a.len() ==> a.spec_index(k) == 'b' || a.spec_index(k) == 'a' || a.spec_index(k) == 'd',
            count_char(result, 'b') == count_char(a.spec_index(0..i), 'b'),
            count_char(result, 'a') == 0,
            count_char(result, 'd') == 0
    {
        if a.as_bytes()[i] == 'b' as u8 {
            result.push('b');
        }
        i = i + 1;
    }
    
    let b_count = result.len();
    
    // Second pass: add all 'a's
    i = 0;
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            result.len() <= a.len(),
            forall|k: int| 0 <= k < b_count ==> result.spec_index(k) == 'b',
            forall|k: int| b_count <= k < result.len() ==> result.spec_index(k) == 'a',
            forall|k: int| 0 <= k < a.len() ==> a.spec_index(k) == 'b' || a.spec_index(k) == 'a' || a.spec_index(k) == 'd',
            count_char(result, 'b') == count_char(a, 'b'),
            count_char(result.spec_index(b_count..result.len()), 'a') == count_char(a.spec_index(0..i), 'a'),
            count_char(result, 'd') == 0
    {
        if a.as_bytes()[i] == 'a' as u8 {
            result.push('a');
        }
        i = i + 1;
    }
    
    let a_count = result.len();
    
    // Third pass: add all 'd's
    i = 0;
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            result.len() <= a.len(),
            forall|k: int| 0 <= k < b_count ==> result.spec_index(k) == 'b',
            forall|k: int| b_count <= k < a_count ==> result.spec_index(k) == 'a',
            forall|k: int| a_count <= k < result.len() ==> result.spec_index(k) == 'd',
            forall|k: int| 0 <= k < a.len() ==> a.spec_index(k) == 'b' || a.spec_index(k) == 'a' || a.spec_index(k) == 'd',
            count_char(result, 'b') == count_char(a, 'b'),
            count_char(result, 'a') == count_char(a, 'a'),
            count_char(result.spec_index(a_count..result.len()), 'd') == count_char(a.spec_index(0..i), 'd')
    {
        if a.as_bytes()[i] == 'd' as u8 {
            result.push('d');
        }
        i = i + 1;
    }
    
    // Prove that the result is sorted
    assert(forall|i: int, j: int| 0 <= i < result.len() && 0 <= j < result.len() && result.spec_index(i) == 'b' && (result.spec_index(j) == 'a' || result.spec_index(j) == 'd') ==> i < j);
    assert(forall|i: int, j: int| 0 <= i < result.len() && 0 <= j < result.len() && result.spec_index(i) == 'a' && result.spec_index(j) == 'b' ==> i > j);
    assert(forall|i: int, j: int| 0 <= i < result.len() && 0 <= j < result.len() && result.spec_index(i) == 'a' && result.spec_index(j) == 'd' ==> i < j);
    assert(forall|i: int, j: int| 0 <= i < result.len() && 0 <= j < result.len() && result.spec_index(i) == 'd' && (result.spec_index(j) == 'a' || result.spec_index(j) == 'b') ==> i > j);
    
    // Prove multiset equality
    assert(count_char(result, 'b') == count_char(a, 'b'));
    assert(count_char(result, 'a') == count_char(a, 'a'));
    assert(count_char(result, 'd') == count_char(a, 'd'));
    assert(result.len() == count_char(result, 'b') + count_char(result, 'a') + count_char(result, 'd'));
    assert(a.len() == count_char(a, 'b') + count_char(a, 'a') + count_char(a, 'd'));
    
    result
}

}