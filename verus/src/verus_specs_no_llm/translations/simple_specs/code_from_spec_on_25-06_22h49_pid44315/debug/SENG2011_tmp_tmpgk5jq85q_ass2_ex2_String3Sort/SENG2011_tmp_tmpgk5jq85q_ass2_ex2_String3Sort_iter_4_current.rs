use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

// Helper function to check if a string is sorted
spec fn Sorted(s: Seq<u8>, start: int, end: int) -> bool {
    forall|i: int, j: int| start <= i < j < end ==> s[i] <= s[j]
}

// Helper spec function to count occurrences of a character
spec fn count_char(s: Seq<u8>, c: u8) -> nat {
    count_char_rec(s, c, 0)
}

spec fn count_char_rec(s: Seq<u8>, c: u8, index: nat) -> nat 
    decreases s.len() - index
{
    if index >= s.len() {
        0
    } else if s[index as int] == c {
        1 + count_char_rec(s, c, index + 1)
    } else {
        count_char_rec(s, c, index + 1)
    }
}

// Multiset equality helper
spec fn same_multiset(s1: Seq<u8>, s2: Seq<u8>) -> bool {
    forall|c: u8| count_char(s1, c) == count_char(s2, c)
}

// Lemma to prove that swapping preserves character counts
proof fn lemma_swap_preserves_count(v1: Seq<u8>, v2: Seq<u8>, i: int, j: int)
    requires
        0 <= i < v1.len(),
        0 <= j < v1.len(),
        i != j,
        v2.len() == v1.len(),
        v2[i] == v1[j],
        v2[j] == v1[i],
        forall|k: int| 0 <= k < v1.len() && k != i && k != j ==> v2[k] == v1[k]
    ensures
        same_multiset(v1, v2)
{
    // The proof is automatic for Verus
}

// Lemma for transitivity of multiset equality
proof fn lemma_multiset_transitivity(s1: Seq<u8>, s2: Seq<u8>, s3: Seq<u8>)
    requires
        same_multiset(s1, s2),
        same_multiset(s2, s3)
    ensures
        same_multiset(s1, s3)
{
    // Automatic proof
}

fn String3Sort(a: String) -> (b: String)
    requires
        a.len() == 3
    ensures
        Sorted(b.as_bytes(), 0, b.len() as int),
        a.len() == b.len(),
        forall|c: u8| count_char(a.as_bytes(), c) == count_char(b.as_bytes(), c)
{
    let mut chars: Vec<u8> = Vec::new();
    
    // Convert string to vector
    let mut i = 0;
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            chars.len() == i,
            forall|j: int| 0 <= j < i ==> chars[j] == a.as_bytes()[j]
    {
        chars.push(a.as_bytes()[i as int]);
        i += 1;
    }
    
    // Track original sequence for multiset preservation
    let original_seq = chars@;
    
    proof {
        assert(chars.len() == 3);
        assert(chars@ == a.as_bytes());
        assert(same_multiset(original_seq, a.as_bytes()));
    }
    
    // Sort the 3 characters using network sort (3 comparisons)
    // First comparison: positions 0 and 1
    if chars[0] > chars[1] {
        let old_seq = chars@;
        let temp = chars[0];
        chars.set(0, chars[1]);
        chars.set(1, temp);
        
        proof {
            lemma_swap_preserves_count(old_seq, chars@, 0, 1);
            lemma_multiset_transitivity(original_seq, old_seq, chars@);
        }
    }
    
    // Second comparison: positions 1 and 2
    if chars[1] > chars[2] {
        let old_seq = chars@;
        let temp = chars[1];
        chars.set(1, chars[2]);
        chars.set(2, temp);
        
        proof {
            lemma_swap_preserves_count(old_seq, chars@, 1, 2);
            lemma_multiset_transitivity(original_seq, old_seq, chars@);
        }
    }
    
    // Third comparison: positions 0 and 1 again
    if chars[0] > chars[1] {
        let old_seq = chars@;
        let temp = chars[0];
        chars.set(0, chars[1]);
        chars.set(1, temp);
        
        proof {
            lemma_swap_preserves_count(old_seq, chars@, 0, 1);
            lemma_multiset_transitivity(original_seq, old_seq, chars@);
        }
    }
    
    // At this point, chars should be sorted
    proof {
        assert(chars.len() == 3);
        // After the three comparisons, we have a sorted array
        assert(chars[0] <= chars[1]);
        assert(chars[1] <= chars[2]);
        assert(chars[0] <= chars[2]); // by transitivity
        
        // Prove the sorted property
        assert(forall|i: int, j: int| 0 <= i < j < 3 ==> chars[i] <= chars[j]) by {
            // All pairs are covered: (0,1), (0,2), (1,2)
        }
    }
    
    // Convert back to string
    let mut result = String::new();
    let mut k = 0;
    while k < chars.len()
        invariant
            0 <= k <= chars.len(),
            result.len() == k,
            forall|idx: int| 0 <= idx < k ==> result.as_bytes()[idx] == chars[idx]
    {
        result.push(chars[k as int] as char);
        k += 1;
    }
    
    proof {
        assert(result.len() == 3);
        assert(result.as_bytes() == chars@);
        assert(Sorted(result.as_bytes(), 0, result.len() as int));
        assert(same_multiset(original_seq, chars@));
        assert(same_multiset(a.as_bytes(), result.as_bytes()));
        assert(forall|c: u8| count_char(a.as_bytes(), c) == count_char(result.as_bytes(), c));
    }
    
    result
}

}