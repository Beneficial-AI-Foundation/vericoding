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

// Helper spec function to count chars up to index i
spec fn count_char_upto(s: Seq<char>, c: char, i: int) -> int
    recommends 0 <= i <= s.len()
{
    count_char(s.subrange(0, i), c)
}

// Helper lemma for count_char properties
proof fn lemma_count_char_properties(s: Seq<char>, c: char)
    ensures count_char(s, c) >= 0
    decreases s.len()
{
    if s.len() > 0 {
        lemma_count_char_properties(s.subrange(1, s.len() as int), c);
    }
}

// Helper lemma for counting specific character when iterating
proof fn lemma_count_iteration(s: Seq<char>, c: char, i: int)
    requires 0 <= i < s.len()
    ensures count_char_upto(s, c, i + 1) == count_char_upto(s, c, i) + (if s[i] == c { 1 } else { 0 })
{
    let prefix_i = s.subrange(0, i);
    let prefix_i_plus_1 = s.subrange(0, i + 1);
    assert(prefix_i_plus_1 =~= prefix_i + seq![s[i]]);
    
    // Prove the counting property by induction on the structure
    lemma_count_append(prefix_i, seq![s[i]], c);
}

// Additional helper lemma for append counting
proof fn lemma_count_append(s1: Seq<char>, s2: Seq<char>, c: char)
    ensures count_char(s1 + s2, c) == count_char(s1, c) + count_char(s2, c)
    decreases s1.len()
{
    if s1.len() == 0 {
        assert(s1 + s2 =~= s2);
    } else {
        let tail = s1.subrange(1, s1.len() as int);
        assert(s1 =~= seq![s1[0]] + tail);
        assert(s1 + s2 =~= seq![s1[0]] + (tail + s2));
        lemma_count_append(tail, s2, c);
    }
}

proof fn lemma_count_total(s: Seq<char>, c: char)
    ensures count_char_upto(s, c, s.len() as int) == count_char(s, c)
{
    assert(s.subrange(0, s.len() as int) =~= s);
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
            count_char(result@, 'b') == count_char_upto(a@, 'b', i as int),
            count_char(result@, 'a') == 0,
            count_char(result@, 'd') == 0,
            result.len() <= a.len()
    {
        proof {
            lemma_count_iteration(a@, 'b', i as int);
        }
        if a[i] == 'b' {
            result.push('b');
        }
        i = i + 1;
    }
    
    let ghost b_count = result.len() as int;
    proof {
        lemma_count_total(a@, 'b');
        assert(count_char(result@, 'b') == count_char(a@, 'b'));
    }
    
    // Second pass: add all 'a's
    i = 0;
    while i < a.len()
        invariant 
            0 <= i <= a.len(),
            result.len() as int == b_count + count_char_upto(a@, 'a', i as int),
            forall|k: int| 0 <= k < b_count ==> result[k] == 'b',
            forall|k: int| b_count <= k < result.len() ==> result[k] == 'a',
            count_char(result@, 'b') == count_char(a@, 'b'),
            count_char(result@, 'a') == count_char_upto(a@, 'a', i as int),
            count_char(result@, 'd') == 0,
            b_count == count_char(a@, 'b'),
            result.len() <= a.len()
    {
        proof {
            lemma_count_iteration(a@, 'a', i as int);
        }
        if a[i] == 'a' {
            result.push('a');
        }
        i = i + 1;
    }
    
    let ghost a_end = result.len() as int;
    proof {
        lemma_count_total(a@, 'a');
        assert(count_char(result@, 'a') == count_char(a@, 'a'));
    }
    
    // Third pass: add all 'd's
    i = 0;
    while i < a.len()
        invariant 
            0 <= i <= a.len(),
            result.len() as int == a_end + count_char_upto(a@, 'd', i as int),
            forall|k: int| 0 <= k < b_count ==> result[k] == 'b',
            forall|k: int| b_count <= k < a_end ==> result[k] == 'a',
            forall|k: int| a_end <= k < result.len() ==> result[k] == 'd',
            count_char(result@, 'b') == count_char(a@, 'b'),
            count_char(result@, 'a') == count_char(a@, 'a'),
            count_char(result@, 'd') == count_char_upto(a@, 'd', i as int),
            b_count == count_char(a@, 'b'),
            a_end == count_char(a@, 'b') + count_char(a@, 'a'),
            result.len() <= a.len()
    {
        proof {
            lemma_count_iteration(a@, 'd', i as int);
        }
        if a[i] == 'd' {
            result.push('d');
        }
        i = i + 1;
    }
    
    // Final proof
    proof {
        lemma_count_total(a@, 'd');
        assert(count_char(result@, 'd') == count_char(a@, 'd'));
        
        // Prove length property
        lemma_total_length(a@);
        assert(count_char(a@, 'b') + count_char(a@, 'a') + count_char(a@, 'd') == a.len());
        assert(result.len() == count_char(a@, 'b') + count_char(a@, 'a') + count_char(a@, 'd'));
        assert(result.len() == a.len());
        
        // Prove sortedbad property using the structure we've built
        lemma_sortedbad_structure(result@, b_count, a_end);
    }
    
    result
}

// Helper lemma to prove the sortedbad property based on the structure
proof fn lemma_sortedbad_structure(s: Seq<char>, b_count: int, a_end: int)
    requires
        0 <= b_count <= a_end <= s.len(),
        forall|k: int| 0 <= k < b_count ==> s[k] == 'b',
        forall|k: int| b_count <= k < a_end ==> s[k] == 'a',
        forall|k: int| a_end <= k < s.len() ==> s[k] == 'd'
    ensures
        sortedbad(s)
{
    // All b's are before all a's and d's
    assert(forall|i: int, j: int| 0 <= i < s.len() && 0 <= j < s.len() && s[i] == 'b' && (s[j] == 'a' || s[j] == 'd') ==> i < j) by {
        assert(forall|i: int| 0 <= i < s.len() && s[i] == 'b' ==> i < b_count);
        assert(forall|j: int| 0 <= j < s.len() && (s[j] == 'a' || s[j] == 'd') ==> j >= b_count);
    };
    
    // All a's are after all b's
    assert(forall|i: int, j: int| 0 <= i < s.len() && 0 <= j < s.len() && s[i] == 'a' && s[j] == 'b' ==> i > j) by {
        assert(forall|i: int| 0 <= i < s.len() && s[i] == 'a' ==> i >= b_count);
        assert(forall|j: int| 0 <= j < s.len() && s[j] == 'b' ==> j < b_count);
    };
    
    // All a's are before all d's
    assert(forall|i: int, j: int| 0 <= i < s.len() && 0 <= j < s.len() && s[i] == 'a' && s[j] == 'd' ==> i < j) by {
        assert(forall|i: int| 0 <= i < s.len() && s[i] == 'a' ==> i < a_end);
        assert(forall|j: int| 0 <= j < s.len() && s[j] == 'd' ==> j >= a_end);
    };
    
    // All d's are after all b's and a's
    assert(forall|i: int, j: int| 0 <= i < s.len() && 0 <= j < s.len() && s[i] == 'd' && (s[j] == 'a' || s[j] == 'b') ==> i > j) by {
        assert(forall|i: int| 0 <= i < s.len() && s[i] == 'd' ==> i >= a_end);
        assert(forall|j: int| 0 <= j < s.len() && (s[j] == 'a' || s[j] == 'b') ==> j < a_end);
    };
}

// Helper lemma to prove total length
proof fn lemma_total_length(s: Seq<char>)
    requires forall|k: int| 0 <= k < s.len() ==> s[k] == 'b' || s[k] == 'a' || s[k] == 'd'
    ensures count_char(s, 'b') + count_char(s, 'a') + count_char(s, 'd') == s.len()
    decreases s.len()
{
    if s.len() == 0 {
        // Base case
    } else {
        let tail = s.subrange(1, s.len() as int);
        assert(forall|k: int| 0 <= k < tail.len() ==> tail[k] == 'b' || tail[k] == 'a' || tail[k] == 'd');
        lemma_total_length(tail);
        
        // The first element must be one of 'b', 'a', or 'd'
        assert(s[0] == 'b' || s[0] == 'a' || s[0] == 'd');
        
        // By definition of count_char
        assert(count_char(s, 'b') == (if s[0] == 'b' { 1 } else { 0 }) + count_char(tail, 'b'));
        assert(count_char(s, 'a') == (if s[0] == 'a' { 1 } else { 0 }) + count_char(tail, 'a'));
        assert(count_char(s, 'd') == (if s[0] == 'd' { 1 } else { 0 }) + count_char(tail, 'd'));
        
        // Since exactly one of the conditions is true, the sum equals 1 + tail.len()
        assert(count_char(s, 'b') + count_char(s, 'a') + count_char(s, 'd') == 1 + count_char(tail, 'b') + count_char(tail, 'a') + count_char(tail, 'd'));
        assert(count_char(s, 'b') + count_char(s, 'a') + count_char(s, 'd') == 1 + tail.len());
        assert(count_char(s, 'b') + count_char(s, 'a') + count_char(s, 'd') == s.len());
    }
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