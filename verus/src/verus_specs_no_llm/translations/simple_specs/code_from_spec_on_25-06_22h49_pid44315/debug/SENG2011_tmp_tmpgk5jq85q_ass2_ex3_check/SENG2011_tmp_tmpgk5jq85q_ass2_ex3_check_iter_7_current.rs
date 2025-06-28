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
            count_char(result@, 'd') == 0
    {
        if a[i] == 'b' {
            result.push('b');
        }
        proof {
            lemma_count_iteration(a@, 'b', i as int);
        }
        i = i + 1;
    }
    
    let ghost b_count = result.len();
    proof {
        lemma_count_total(a@, 'b');
        assert(count_char(result@, 'b') == count_char(a@, 'b'));
    }
    
    // Second pass: add all 'a's
    i = 0;
    while i < a.len()
        invariant 
            0 <= i <= a.len(),
            result.len() == b_count + count_char_upto(a@, 'a', i as int),
            forall|k: int| 0 <= k < b_count ==> result[k] == 'b',
            forall|k: int| b_count <= k < result.len() ==> result[k] == 'a',
            count_char(result@, 'b') == count_char(a@, 'b'),
            count_char(result@, 'a') == count_char_upto(a@, 'a', i as int),
            count_char(result@, 'd') == 0,
            b_count == count_char(a@, 'b')
    {
        if a[i] == 'a' {
            result.push('a');
        }
        proof {
            lemma_count_iteration(a@, 'a', i as int);
        }
        i = i + 1;
    }
    
    let ghost a_end = result.len();
    proof {
        lemma_count_total(a@, 'a');
        assert(count_char(result@, 'a') == count_char(a@, 'a'));
    }
    
    // Third pass: add all 'd's
    i = 0;
    while i < a.len()
        invariant 
            0 <= i <= a.len(),
            result.len() == a_end + count_char_upto(a@, 'd', i as int),
            forall|k: int| 0 <= k < b_count ==> result[k] == 'b',
            forall|k: int| b_count <= k < a_end ==> result[k] == 'a',
            forall|k: int| a_end <= k < result.len() ==> result[k] == 'd',
            count_char(result@, 'b') == count_char(a@, 'b'),
            count_char(result@, 'a') == count_char(a@, 'a'),
            count_char(result@, 'd') == count_char_upto(a@, 'd', i as int),
            b_count == count_char(a@, 'b'),
            a_end == count_char(a@, 'b') + count_char(a@, 'a')
    {
        if a[i] == 'd' {
            result.push('d');
        }
        proof {
            lemma_count_iteration(a@, 'd', i as int);
        }
        i = i + 1;
    }
    
    // Final proof
    proof {
        lemma_count_total(a@, 'd');
        assert(count_char(result@, 'd') == count_char(a@, 'd'));
        
        // Prove length property
        assert(count_char(a@, 'b') + count_char(a@, 'a') + count_char(a@, 'd') == a.len()) by {
            let mut total = 0;
            let mut j = 0;
            while j < a.len()
                invariant 
                    0 <= j <= a.len(),
                    total == count_char_upto(a@, 'b', j as int) + count_char_upto(a@, 'a', j as int) + count_char_upto(a@, 'd', j as int)
            {
                if a[j] == 'b' || a[j] == 'a' || a[j] == 'd' {
                    total = total + 1;
                }
                proof {
                    lemma_count_iteration(a@, 'b', j as int);
                    lemma_count_iteration(a@, 'a', j as int);
                    lemma_count_iteration(a@, 'd', j as int);
                }
                j = j + 1;
            }
            lemma_count_total(a@, 'b');
            lemma_count_total(a@, 'a');
            lemma_count_total(a@, 'd');
        };
        
        // Prove sortedbad property
        assert(forall|j: int, k: int| 0 <= j < result.len() && 0 <= k < result.len() && result[j] == 'b' && (result[k] == 'a' || result[k] == 'd') ==> j < k) by {
            assert(forall|j: int| 0 <= j < result.len() && result[j] == 'b' ==> j < b_count);
            assert(forall|k: int| 0 <= k < result.len() && (result[k] == 'a' || result[k] == 'd') ==> k >= b_count);
        };
        
        assert(forall|j: int, k: int| 0 <= j < result.len() && 0 <= k < result.len() && result[j] == 'a' && result[k] == 'b' ==> j > k) by {
            assert(forall|j: int| 0 <= j < result.len() && result[j] == 'a' ==> j >= b_count);
            assert(forall|k: int| 0 <= k < result.len() && result[k] == 'b' ==> k < b_count);
        };
        
        assert(forall|j: int, k: int| 0 <= j < result.len() && 0 <= k < result.len() && result[j] == 'a' && result[k] == 'd' ==> j < k) by {
            assert(forall|j: int| 0 <= j < result.len() && result[j] == 'a' ==> b_count <= j < a_end);
            assert(forall|k: int| 0 <= k < result.len() && result[k] == 'd' ==> k >= a_end);
        };
        
        assert(forall|j: int, k: int| 0 <= j < result.len() && 0 <= k < result.len() && result[j] == 'd' && (result[k] == 'a' || result[k] == 'b') ==> j > k) by {
            assert(forall|j: int| 0 <= j < result.len() && result[j] == 'd' ==> j >= a_end);
            assert(forall|k: int| 0 <= k < result.len() && (result[k] == 'a' || result[k] == 'b') ==> k < a_end);
        };
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