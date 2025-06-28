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
proof fn lemma_count_char_split(s: Seq<char>, c: char, i: int)
    requires 0 <= i <= s.len()
    ensures count_char(s, c) == count_char(s.subrange(0, i), c) + count_char(s.subrange(i, s.len() as int), c)
    decreases i
{
    if i == 0 {
        assert(s.subrange(0, 0) =~= seq![]);
        assert(s.subrange(0, s.len() as int) =~= s);
    } else if i == s.len() {
        assert(s.subrange(s.len() as int, s.len() as int) =~= seq![]);
        assert(s.subrange(0, s.len() as int) =~= s);
    } else {
        lemma_count_char_split(s, c, i - 1);
        let prefix = s.subrange(0, i - 1);
        let middle = seq![s[i - 1]];
        let suffix = s.subrange(i, s.len() as int);
        assert(s =~= prefix + middle + suffix);
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
        proof {
            lemma_count_iteration(a@, 'b', i as int);
        }
        if a[i] == 'b' {
            result.push('b');
        }
        i = i + 1;
    }
    
    let ghost b_count = result.len();
    proof {
        lemma_count_char_split(a@, 'b', a.len() as int);
        assert(count_char_upto(a@, 'b', a.len() as int) == count_char(a@, 'b'));
    }
    
    // Second pass: add all 'a's
    i = 0;
    while i < a.len()
        invariant 
            0 <= i <= a.len(),
            b_count == result.len() - count_char_upto(a@, 'a', i as int),
            result.len() == count_char(a@, 'b') + count_char_upto(a@, 'a', i as int),
            forall|k: int| 0 <= k < b_count ==> result[k] == 'b',
            forall|k: int| b_count <= k < result.len() ==> result[k] == 'a',
            count_char(result@, 'b') == count_char(a@, 'b'),
            count_char(result@, 'a') == count_char_upto(a@, 'a', i as int),
            count_char(result@, 'd') == 0
    {
        proof {
            lemma_count_iteration(a@, 'a', i as int);
        }
        if a[i] == 'a' {
            result.push('a');
        }
        i = i + 1;
    }
    
    let ghost a_end = result.len();
    proof {
        lemma_count_char_split(a@, 'a', a.len() as int);
        assert(count_char_upto(a@, 'a', a.len() as int) == count_char(a@, 'a'));
    }
    
    // Third pass: add all 'd's
    i = 0;
    while i < a.len()
        invariant 
            0 <= i <= a.len(),
            a_end == result.len() - count_char_upto(a@, 'd', i as int),
            result.len() == count_char(a@, 'b') + count_char(a@, 'a') + count_char_upto(a@, 'd', i as int),
            forall|k: int| 0 <= k < b_count ==> result[k] == 'b',
            forall|k: int| b_count <= k < a_end ==> result[k] == 'a',
            forall|k: int| a_end <= k < result.len() ==> result[k] == 'd',
            count_char(result@, 'b') == count_char(a@, 'b'),
            count_char(result@, 'a') == count_char(a@, 'a'),
            count_char(result@, 'd') == count_char_upto(a@, 'd', i as int)
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
        lemma_count_char_split(a@, 'd', a.len() as int);
        assert(count_char_upto(a@, 'd', a.len() as int) == count_char(a@, 'd'));
        
        // Prove sortedbad property from the structure
        assert(forall|j: int, k: int| 0 <= j < result.len() && 0 <= k < result.len() && result[j] == 'b' && (result[k] == 'a' || result[k] == 'd') ==> {
            &&& j < b_count  // j is in b section
            &&& k >= b_count  // k is in a or d section
            &&& j < k
        });
        
        assert(forall|j: int, k: int| 0 <= j < result.len() && 0 <= k < result.len() && result[j] == 'a' && result[k] == 'b' ==> {
            &&& j >= b_count  // j is in a section
            &&& k < b_count   // k is in b section
            &&& j > k
        });
        
        assert(forall|j: int, k: int| 0 <= j < result.len() && 0 <= k < result.len() && result[j] == 'a' && result[k] == 'd' ==> {
            &&& b_count <= j < a_end  // j is in a section
            &&& k >= a_end            // k is in d section
            &&& j < k
        });
        
        assert(forall|j: int, k: int| 0 <= j < result.len() && 0 <= k < result.len() && result[j] == 'd' && (result[k] == 'a' || result[k] == 'b') ==> {
            &&& j >= a_end    // j is in d section
            &&& k < a_end     // k is in b or a section
            &&& j > k
        });
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