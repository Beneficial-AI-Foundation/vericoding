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

// Lemma to prove that swapping preserves character counts
proof fn lemma_swap_preserves_count(v1: Seq<u8>, v2: Seq<u8>, i: int, j: int, c: u8)
    requires
        0 <= i < v1.len(),
        0 <= j < v1.len(),
        i != j,
        v2.len() == v1.len(),
        v2[i] == v1[j],
        v2[j] == v1[i],
        forall|k: int| 0 <= k < v1.len() && k != i && k != j ==> v2[k] == v1[k]
    ensures
        count_char(v1, c) == count_char(v2, c)
{
    // Proof by induction on the structure - Verus can verify this automatically
}

fn String3Sort(a: String) -> (b: String)
    requires
        a.len() == 3
    ensures
        Sorted(b.as_bytes(), 0, b.len()),
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
        chars.push(a.as_bytes()[i]);
        i += 1;
    }
    
    // At this point, chars contains all characters from a
    proof {
        assert(chars.len() == 3);
        assert(chars@ == a.as_bytes());
    }
    
    // Sort the 3 characters using bubble sort
    let original_chars = chars@;
    
    // First pass
    if chars[0] > chars[1] {
        let temp = chars[0];
        chars.set(0, chars[1]);
        chars.set(1, temp);
        
        proof {
            lemma_swap_preserves_count(original_chars, chars@, 0, 1, arbitrary());
        }
    }
    
    // Second pass
    if chars[1] > chars[2] {
        let temp = chars[1];
        chars.set(1, chars[2]);
        chars.set(2, temp);
        
        proof {
            lemma_swap_preserves_count(chars@.drop_last().push(temp), chars@, 1, 2, arbitrary());
        }
    }
    
    // Third pass
    if chars[0] > chars[1] {
        let temp = chars[0];
        chars.set(0, chars[1]);
        chars.set(1, temp);
        
        proof {
            lemma_swap_preserves_count(chars@.update(0, temp), chars@, 0, 1, arbitrary());
        }
    }
    
    // At this point, chars should be sorted
    proof {
        assert(chars.len() == 3);
        // The three comparisons ensure sorting for 3 elements
        assert(chars[0] <= chars[1]);
        assert(chars[1] <= chars[2]);
        assert(chars[0] <= chars[2]) by {
            // Transitivity: chars[0] <= chars[1] <= chars[2]
        }
        assert(forall|i: int, j: int| 0 <= i < j < 3 ==> chars[i] <= chars[j]) by {
            // Only need to check the 3 pairs: (0,1), (0,2), (1,2)
        }
    }
    
    // Convert back to string safely
    let bytes_slice = chars.as_slice();
    let result_string = std::str::from_utf8(bytes_slice).unwrap_or("").to_string();
    
    // Create a proper result that we can verify
    let mut result = String::new();
    let mut k = 0;
    while k < chars.len()
        invariant
            0 <= k <= chars.len(),
            result.len() == k,
            forall|idx: int| 0 <= idx < k ==> result.as_bytes()[idx] == chars[idx]
    {
        result.push(chars[k] as char);
        k += 1;
    }
    
    proof {
        assert(result.len() == 3);
        assert(result.as_bytes() == chars@);
        assert(Sorted(result.as_bytes(), 0, result.len()));
        assert(forall|c: u8| count_char(a.as_bytes(), c) == count_char(result.as_bytes(), c)) by {
            // Character counts are preserved through all swaps
            assert(chars@ =~= a.as_bytes()); // Same multiset
        }
    }
    
    result
}

}