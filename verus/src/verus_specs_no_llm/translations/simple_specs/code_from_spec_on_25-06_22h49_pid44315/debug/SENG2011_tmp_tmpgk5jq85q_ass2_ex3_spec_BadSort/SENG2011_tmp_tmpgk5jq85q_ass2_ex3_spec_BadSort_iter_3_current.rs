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
        count_char(s.subrange(1, s.len() as int), c) + 
        if s[0] == c { 1 } else { 0 }
    }
}

fn BadSort(a: Vec<char>) -> (b: Vec<char>)
    requires
        forall|k: int| 0 <= k < a.len() ==> a[k] == 'b' || a[k] == 'a' || a[k] == 'd'
    ensures
        sortedbad(b@),
        multiset(a@) == multiset(b@),
        a.len() == b.len()
{
    let mut result: Vec<char> = Vec::new();
    let mut i: usize = 0;
    
    // First pass: add all 'b's
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            result.len() <= a.len(),
            forall|k: int| 0 <= k < result.len() ==> result[k] == 'b',
            forall|k: int| 0 <= k < a.len() ==> a[k] == 'b' || a[k] == 'a' || a[k] == 'd',
            count_char(result@, 'b') == count_char(a@.subrange(0, i as int), 'b'),
            count_char(result@, 'a') == 0,
            count_char(result@, 'd') == 0
    {
        if a[i] == 'b' {
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
            b_count <= result.len(),
            forall|k: int| 0 <= k < b_count ==> result[k] == 'b',
            forall|k: int| b_count <= k < result.len() ==> result[k] == 'a',
            forall|k: int| 0 <= k < a.len() ==> a[k] == 'b' || a[k] == 'a' || a[k] == 'd',
            count_char(result@, 'b') == count_char(a@, 'b'),
            count_char(result@.subrange(b_count as int, result.len() as int), 'a') == count_char(a@.subrange(0, i as int), 'a'),
            count_char(result@, 'd') == 0
    {
        if a[i] == 'a' {
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
            b_count <= a_count <= result.len(),
            forall|k: int| 0 <= k < b_count ==> result[k] == 'b',
            forall|k: int| b_count <= k < a_count ==> result[k] == 'a',
            forall|k: int| a_count <= k < result.len() ==> result[k] == 'd',
            forall|k: int| 0 <= k < a.len() ==> a[k] == 'b' || a[k] == 'a' || a[k] == 'd',
            count_char(result@, 'b') == count_char(a@, 'b'),
            count_char(result@, 'a') == count_char(a@, 'a'),
            count_char(result@.subrange(a_count as int, result.len() as int), 'd') == count_char(a@.subrange(0, i as int), 'd')
    {
        if a[i] == 'd' {
            result.push('d');
        }
        i = i + 1;
    }
    
    // Prove that the final result has the correct character counts
    proof {
        assert(count_char(result@, 'b') == count_char(a@, 'b'));
        assert(count_char(result@, 'a') == count_char(a@, 'a'));
        assert(count_char(result@, 'd') == count_char(a@, 'd'));
        
        // Prove length equality
        assert(result.len() == count_char(result@, 'b') + count_char(result@, 'a') + count_char(result@, 'd')) by {
            assert(forall|k: int| 0 <= k < result.len() ==> 
                result[k] == 'b' || result[k] == 'a' || result[k] == 'd');
        };
        
        assert(a.len() == count_char(a@, 'b') + count_char(a@, 'a') + count_char(a@, 'd')) by {
            assert(forall|k: int| 0 <= k < a.len() ==> 
                a[k] == 'b' || a[k] == 'a' || a[k] == 'd');
        };
        
        // Prove sorting property
        assert(forall|i: int, j: int| 0 <= i < result.len() && 0 <= j < result.len() && 
            result@[i] == 'b' && (result@[j] == 'a' || result@[j] == 'd') ==> i < j) by {
            assert(forall|k: int| 0 <= k < b_count ==> result@[k] == 'b');
            assert(forall|k: int| b_count <= k < result.len() ==> result@[k] != 'b');
        };
        
        assert(forall|i: int, j: int| 0 <= i < result.len() && 0 <= j < result.len() && 
            result@[i] == 'a' && result@[j] == 'b' ==> i > j) by {
            assert(forall|k: int| 0 <= k < b_count ==> result@[k] == 'b');
            assert(forall|k: int| b_count <= k < a_count ==> result@[k] == 'a');
        };
        
        assert(forall|i: int, j: int| 0 <= i < result.len() && 0 <= j < result.len() && 
            result@[i] == 'a' && result@[j] == 'd' ==> i < j) by {
            assert(forall|k: int| b_count <= k < a_count ==> result@[k] == 'a');
            assert(forall|k: int| a_count <= k < result.len() ==> result@[k] == 'd');
        };
        
        assert(forall|i: int, j: int| 0 <= i < result.len() && 0 <= j < result.len() && 
            result@[i] == 'd' && (result@[j] == 'a' || result@[j] == 'b') ==> i > j) by {
            assert(forall|k: int| a_count <= k < result.len() ==> result@[k] == 'd');
            assert(forall|k: int| 0 <= k < a_count ==> result@[k] != 'd');
        };
    }
    
    result
}

}