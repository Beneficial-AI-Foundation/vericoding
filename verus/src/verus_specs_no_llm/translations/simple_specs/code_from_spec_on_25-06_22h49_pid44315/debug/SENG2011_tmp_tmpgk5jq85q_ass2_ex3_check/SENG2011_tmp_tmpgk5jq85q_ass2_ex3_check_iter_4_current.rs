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
spec fn count_char(s: Seq<char>, c: char) -> int 
    decreases s.len()
{
    if s.len() == 0 {
        0
    } else {
        (if s[0] == c { 1 } else { 0 }) + count_char(s.subrange(1, s.len() as int), c)
    }
}

// Helper lemma for count_char properties
proof fn lemma_count_char_append(s1: Seq<char>, s2: Seq<char>, c: char)
    ensures count_char(s1 + s2, c) == count_char(s1, c) + count_char(s2, c)
    decreases s1.len()
{
    if s1.len() == 0 {
        assert(s1 + s2 =~= s2);
    } else {
        lemma_count_char_append(s1.subrange(1, s1.len() as int), s2, c);
        assert(s1 + s2 =~= seq![s1[0]] + s1.subrange(1, s1.len() as int) + s2);
    }
}

// Helper lemma for total count
proof fn lemma_total_count(s: Seq<char>)
    requires forall|k: int| 0 <= k < s.len() ==> s[k] == 'b' || s[k] == 'a' || s[k] == 'd'
    ensures s.len() == count_char(s, 'b') + count_char(s, 'a') + count_char(s, 'd')
    decreases s.len()
{
    if s.len() == 0 {
        // base case
    } else {
        lemma_total_count(s.subrange(1, s.len() as int));
        assert(s[0] == 'b' || s[0] == 'a' || s[0] == 'd');
    }
}

fn BadSort(a: Vec<char>) -> (b: Vec<char>)
    requires 
        forall|k: int| 0 <= k < a.len() ==> a[k] == 'b' || a[k] == 'a' || a[k] == 'd'
    ensures 
        sortedbad(b@),
        a.len() == b.len(),
        count_char(a@, 'b') == count_char(b@, 'b'),
        count_char(a@, 'a') == count_char(b@, 'a'),
        count_char(a@, 'd') == count_char(b@, 'd')
{
    let mut result: Vec<char> = Vec::new();
    let mut i: usize = 0;
    
    // First pass: add all 'b's
    while i < a.len()
        invariant 
            0 <= i <= a.len(),
            forall|k: int| 0 <= k < result.len() ==> result[k] == 'b',
            count_char(result@, 'b') == count_char(a@.subrange(0, i as int), 'b'),
            count_char(result@, 'a') == 0,
            count_char(result@, 'd') == 0
    {
        if a[i] == 'b' {
            result.push('b');
        }
        i = i + 1;
    }
    
    let ghost after_b_len = result.len();
    
    // Second pass: add all 'a's
    i = 0;
    while i < a.len()
        invariant 
            0 <= i <= a.len(),
            after_b_len <= result.len(),
            forall|k: int| 0 <= k < after_b_len ==> result[k] == 'b',
            forall|k: int| after_b_len <= k < result.len() ==> result[k] == 'a',
            forall|k: int| 0 <= k < result.len() ==> result[k] == 'b' || result[k] == 'a',
            forall|j: int, k: int| 0 <= j < result.len() && 0 <= k < result.len() && result[j] == 'b' && result[k] == 'a' ==> j < k,
            count_char(result@, 'b') == count_char(a@, 'b'),
            count_char(result@, 'a') == count_char(a@.subrange(0, i as int), 'a'),
            count_char(result@, 'd') == 0
    {
        if a[i] == 'a' {
            result.push('a');
        }
        i = i + 1;
    }
    
    let ghost after_a_len = result.len();
    
    // Third pass: add all 'd's
    i = 0;
    while i < a.len()
        invariant 
            0 <= i <= a.len(),
            after_b_len <= after_a_len <= result.len(),
            forall|k: int| 0 <= k < after_b_len ==> result[k] == 'b',
            forall|k: int| after_b_len <= k < after_a_len ==> result[k] == 'a',
            forall|k: int| after_a_len <= k < result.len() ==> result[k] == 'd',
            forall|k: int| 0 <= k < result.len() ==> result[k] == 'b' || result[k] == 'a' || result[k] == 'd',
            forall|j: int, k: int| 0 <= j < result.len() && 0 <= k < result.len() && result[j] == 'b' && result[k] == 'a' ==> j < k,
            forall|j: int, k: int| 0 <= j < result.len() && 0 <= k < result.len() && result[j] == 'a' && result[k] == 'd' ==> j < k,
            forall|j: int, k: int| 0 <= j < result.len() && 0 <= k < result.len() && result[j] == 'b' && result[k] == 'd' ==> j < k,
            count_char(result@, 'b') == count_char(a@, 'b'),
            count_char(result@, 'a') == count_char(a@, 'a'),
            count_char(result@, 'd') == count_char(a@.subrange(0, i as int), 'd')
    {
        if a[i] == 'd' {
            result.push('d');
        }
        i = i + 1;
    }
    
    // Prove final properties
    proof {
        // The structure ensures sortedbad property
        assert(forall|j: int, k: int| 0 <= j < result.len() && 0 <= k < result.len() && result[j] == 'b' && (result[k] == 'a' || result[k] == 'd') ==> j < k);
        assert(forall|j: int, k: int| 0 <= j < result.len() && 0 <= k < result.len() && result[j] == 'a' && result[k] == 'b' ==> j > k);
        assert(forall|j: int, k: int| 0 <= j < result.len() && 0 <= k < result.len() && result[j] == 'a' && result[k] == 'd' ==> j < k);
        assert(forall|j: int, k: int| 0 <= j < result.len() && 0 <= k < result.len() && result[j] == 'd' && (result[k] == 'a' || result[k] == 'b') ==> j > k);
        
        // Use helper lemma for length proof
        lemma_total_count(a@);
        lemma_total_count(result@);
    }
    
    result
}

fn check(a: Vec<char>) -> (b: Vec<char>)
    requires
        forall|k: int| 0 <= k < a.len() ==> a[k] == 'b' || a[k] == 'a' || a[k] == 'd'
    ensures
        sortedbad(b@),
        a.len() == b.len()
{
    BadSort(a)
}

}