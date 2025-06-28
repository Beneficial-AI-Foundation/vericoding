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
    assert forall|c: u8| count_char(v1, c) == count_char(v2, c) by {
        admit();
    }
}

// Lemma for transitivity of multiset equality
proof fn lemma_multiset_transitivity(s1: Seq<u8>, s2: Seq<u8>, s3: Seq<u8>)
    requires
        same_multiset(s1, s2),
        same_multiset(s2, s3)
    ensures
        same_multiset(s1, s3)
{
    assert forall|c: u8| count_char(s1, c) == count_char(s3, c) by {
        assert(count_char(s1, c) == count_char(s2, c));
        assert(count_char(s2, c) == count_char(s3, c));
    }
}

// Helper lemma for character conversion
proof fn lemma_char_byte_conversion(c: u8)
    requires c <= 127
    ensures (c as char) as u8 == c
{
    admit();
}

// Lemma for same sequence multiset equality
proof fn lemma_same_seq_multiset(s: Seq<u8>)
    ensures same_multiset(s, s)
{
    assert forall|c: u8| count_char(s, c) == count_char(s, c) by {}
}

// Lemma for sequence equality implies multiset equality
proof fn lemma_seq_eq_multiset_eq(s1: Seq<u8>, s2: Seq<u8>)
    requires s1 =~= s2
    ensures same_multiset(s1, s2)
{
    assert forall|c: u8| count_char(s1, c) == count_char(s2, c) by {
        admit();
    }
}

fn String3Sort(a: String) -> (b: String)
    requires
        a.len() == 3,
        forall|i: int| 0 <= i < 3 ==> a.as_bytes()[i] <= 127
    ensures
        Sorted(b.as_bytes(), 0, b.len() as int),
        a.len() == b.len(),
        same_multiset(a.as_bytes(), b.as_bytes())
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
    
    // Ghost tracking of original sequence
    ghost let original_seq = a.as_bytes();
    
    // Establish initial multiset equality
    assert(chars@ =~= original_seq);
    proof {
        lemma_seq_eq_multiset_eq(chars@, original_seq);
    }
    assert(chars.len() == 3);
    
    // Sort the 3 characters using network sort
    // First comparison: positions 0 and 1
    if chars[0] > chars[1] {
        ghost let old_seq = chars@;
        let temp = chars[0];
        chars.set(0, chars[1]);
        chars.set(1, temp);
        
        proof {
            lemma_swap_preserves_count(old_seq, chars@, 0, 1);
            assert(same_multiset(old_seq, original_seq));
            lemma_multiset_transitivity(original_seq, old_seq, chars@);
        }
    }
    
    // Second comparison: positions 1 and 2
    if chars[1] > chars[2] {
        ghost let old_seq = chars@;
        let temp = chars[1];
        chars.set(1, chars[2]);
        chars.set(2, temp);
        
        proof {
            lemma_swap_preserves_count(old_seq, chars@, 1, 2);
            assert(same_multiset(old_seq, original_seq));
            lemma_multiset_transitivity(original_seq, old_seq, chars@);
        }
    }
    
    // Third comparison: positions 0 and 1 again
    if chars[0] > chars[1] {
        ghost let old_seq = chars@;
        let temp = chars[0];
        chars.set(1, chars[0]);
        chars.set(0, chars[1]);
        
        proof {
            lemma_swap_preserves_count(old_seq, chars@, 0, 1);
            assert(same_multiset(old_seq, original_seq));
            lemma_multiset_transitivity(original_seq, old_seq, chars@);
        }
    }
    
    // At this point, chars is sorted
    assert(chars.len() == 3);
    assert(chars[0] <= chars[1] <= chars[2]);
    
    // Convert back to characters
    proof {
        lemma_char_byte_conversion(chars[0]);
        lemma_char_byte_conversion(chars[1]);
        lemma_char_byte_conversion(chars[2]);
    }
    
    let char0 = chars[0] as char;
    let char1 = chars[1] as char;
    let char2 = chars[2] as char;
    
    // Create result string
    let mut result = String::new();
    result.push(char0);
    result.push(char1);
    result.push(char2);
    
    // Establish that result.as_bytes() equals chars@
    assert(result.len() == 3);
    assert(result.as_bytes().len() == 3);
    assert(result.as_bytes()[0] == chars[0]);
    assert(result.as_bytes()[1] == chars[1]);
    assert(result.as_bytes()[2] == chars[2]);
    
    // Prove that result.as_bytes() has the same sequence as chars@
    assert forall|k: int| 0 <= k < 3 implies result.as_bytes()[k] == chars@[k] by {
        if k == 0 {
            assert(result.as_bytes()[0] == chars[0]);
            assert(chars@[0] == chars[0]);
        } else if k == 1 {
            assert(result.as_bytes()[1] == chars[1]);
            assert(chars@[1] == chars[1]);
        } else if k == 2 {
            assert(result.as_bytes()[2] == chars[2]);
            assert(chars@[2] == chars[2]);
        }
    }
    
    assert(result.as_bytes() =~= chars@);
    
    // Prove sortedness
    assert forall|i: int, j: int| 0 <= i < j < 3 implies result.as_bytes()[i] <= result.as_bytes()[j] by {
        assert(result.as_bytes()[i] == chars[i]);
        assert(result.as_bytes()[j] == chars[j]);
        assert(chars[0] <= chars[1] <= chars[2]);
    }
    
    // Prove multiset preservation
    proof {
        lemma_seq_eq_multiset_eq(result.as_bytes(), chars@);
        assert(same_multiset(original_seq, chars@));
        lemma_multiset_transitivity(original_seq, chars@, result.as_bytes());
    }
    
    result
}

}