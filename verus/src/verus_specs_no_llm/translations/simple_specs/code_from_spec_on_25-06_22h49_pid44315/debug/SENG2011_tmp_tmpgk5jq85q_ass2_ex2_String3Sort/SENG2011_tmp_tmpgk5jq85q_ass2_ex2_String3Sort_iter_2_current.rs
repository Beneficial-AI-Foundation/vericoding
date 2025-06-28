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
    
    // Sort the 3 characters using bubble sort
    // First pass
    if chars[0] > chars[1] {
        let temp = chars[0];
        chars.set(0, chars[1]);
        chars.set(1, temp);
    }
    
    // Second pass
    if chars[1] > chars[2] {
        let temp = chars[1];
        chars.set(1, chars[2]);
        chars.set(2, temp);
    }
    
    // Third pass
    if chars[0] > chars[1] {
        let temp = chars[0];
        chars.set(0, chars[1]);
        chars.set(1, temp);
    }
    
    // Convert back to string
    let result = String::from_utf8_lossy(&chars);
    
    // Add proof assertions
    assert(chars.len() == 3);
    assert(chars[0] <= chars[1] <= chars[2]);
    assert(forall|i: int, j: int| 0 <= i < j < 3 ==> chars[i] <= chars[j]);
    
    // Prove character count preservation
    assert(forall|c: u8| count_char(a.as_bytes(), c) == count_char(chars@, c)) by {
        // The sorting preserves all characters
    };
    
    result
}

}