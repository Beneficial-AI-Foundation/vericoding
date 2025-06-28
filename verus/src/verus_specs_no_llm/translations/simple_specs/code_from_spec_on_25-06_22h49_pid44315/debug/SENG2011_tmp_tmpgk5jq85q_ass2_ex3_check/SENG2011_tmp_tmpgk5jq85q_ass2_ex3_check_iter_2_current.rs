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
        count_char(s.spec_substring(0, s.len() - 1), c) + 
        if s.spec_index(s.len() - 1) == c { 1 } else { 0 }
    }
}

fn BadSort(a: String) -> (b: String)
    requires 
        forall|k: int| 0 <= k < a.len() ==> a.spec_index(k) == 'b' || a.spec_index(k) == 'a' || a.spec_index(k) == 'd'
    ensures 
        sortedbad(b),
        a.len() == b.len(),
        count_char(a, 'b') == count_char(b, 'b'),
        count_char(a, 'a') == count_char(b, 'a'),
        count_char(a, 'd') == count_char(b, 'd')
{
    let mut result = String::new();
    let mut i = 0;
    let b_count = count_char(a, 'b');
    let a_count = count_char(a, 'a');
    let d_count = count_char(a, 'd');
    
    // First pass: add all 'b's
    while i < a.len()
        invariant 
            0 <= i <= a.len(),
            forall|k: int| 0 <= k < result.len() ==> result.spec_index(k) == 'b',
            count_char(result, 'b') == count_char(a.spec_substring(0, i), 'b'),
            count_char(result, 'a') == 0,
            count_char(result, 'd') == 0
    {
        if a.spec_index(i) == 'b' {
            result.push('b');
        }
        i = i + 1;
    }
    
    let after_b_len = result.len();
    
    // Second pass: add all 'a's
    i = 0;
    while i < a.len()
        invariant 
            0 <= i <= a.len(),
            after_b_len <= result.len(),
            forall|k: int| 0 <= k < after_b_len ==> result.spec_index(k) == 'b',
            forall|k: int| after_b_len <= k < result.len() ==> result.spec_index(k) == 'a',
            forall|k: int| 0 <= k < result.len() ==> result.spec_index(k) == 'b' || result.spec_index(k) == 'a',
            forall|j: int, k: int| 0 <= j < result.len() && 0 <= k < result.len() && result.spec_index(j) == 'b' && result.spec_index(k) == 'a' ==> j < k,
            count_char(result, 'b') == b_count,
            count_char(result, 'a') == count_char(a.spec_substring(0, i), 'a'),
            count_char(result, 'd') == 0
    {
        if a.spec_index(i) == 'a' {
            result.push('a');
        }
        i = i + 1;
    }
    
    let after_a_len = result.len();
    
    // Third pass: add all 'd's
    i = 0;
    while i < a.len()
        invariant 
            0 <= i <= a.len(),
            after_b_len <= after_a_len <= result.len(),
            forall|k: int| 0 <= k < after_b_len ==> result.spec_index(k) == 'b',
            forall|k: int| after_b_len <= k < after_a_len ==> result.spec_index(k) == 'a',
            forall|k: int| after_a_len <= k < result.len() ==> result.spec_index(k) == 'd',
            forall|k: int| 0 <= k < result.len() ==> result.spec_index(k) == 'b' || result.spec_index(k) == 'a' || result.spec_index(k) == 'd',
            forall|j: int, k: int| 0 <= j < result.len() && 0 <= k < result.len() && result.spec_index(j) == 'b' && result.spec_index(k) == 'a' ==> j < k,
            forall|j: int, k: int| 0 <= j < result.len() && 0 <= k < result.len() && result.spec_index(j) == 'a' && result.spec_index(k) == 'd' ==> j < k,
            forall|j: int, k: int| 0 <= j < result.len() && 0 <= k < result.len() && result.spec_index(j) == 'b' && result.spec_index(k) == 'd' ==> j < k,
            count_char(result, 'b') == b_count,
            count_char(result, 'a') == a_count,
            count_char(result, 'd') == count_char(a.spec_substring(0, i), 'd')
    {
        if a.spec_index(i) == 'd' {
            result.push('d');
        }
        i = i + 1;
    }
    
    // At this point, we need to prove that result satisfies sortedbad
    assert(forall|j: int, k: int| 0 <= j < result.len() && 0 <= k < result.len() && result.spec_index(j) == 'b' && (result.spec_index(k) == 'a' || result.spec_index(k) == 'd') ==> j < k);
    assert(forall|j: int, k: int| 0 <= j < result.len() && 0 <= k < result.len() && result.spec_index(j) == 'a' && result.spec_index(k) == 'b' ==> j > k);
    assert(forall|j: int, k: int| 0 <= j < result.len() && 0 <= k < result.len() && result.spec_index(j) == 'a' && result.spec_index(k) == 'd' ==> j < k);
    assert(forall|j: int, k: int| 0 <= j < result.len() && 0 <= k < result.len() && result.spec_index(j) == 'd' && (result.spec_index(k) == 'a' || result.spec_index(k) == 'b') ==> j > k);
    
    // Prove length equality
    assert(result.len() == b_count + a_count + d_count);
    assert(a.len() == count_char(a, 'b') + count_char(a, 'a') + count_char(a, 'd'));
    
    result
}

fn check(a: String) -> (b: String)
    requires
        forall|k: int| 0 <= k < a.len() ==> a.spec_index(k) == 'b' || a.spec_index(k) == 'a' || a.spec_index(k) == 'd'
    ensures
        sortedbad(b),
        a.len() == b.len()
{
    BadSort(a)
}

}