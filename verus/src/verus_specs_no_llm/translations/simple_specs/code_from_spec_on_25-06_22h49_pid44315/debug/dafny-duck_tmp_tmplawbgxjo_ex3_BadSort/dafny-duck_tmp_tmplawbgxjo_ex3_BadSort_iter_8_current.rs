use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

// Helper function to convert char to int for comparison
spec fn char_to_int(c: char) -> int {
    c as int
}

fn BadSort(a: String) -> (b: String)
    requires
        forall|i: int| 0 <= i < a.len() ==> a@[i] >= '0' && a@[i] <= '9'
    ensures
        b.len() == a.len(),
        forall|i: int| 0 <= i < a.len() ==> b@[i] >= '0' && b@[i] <= '9'
{
    if a.len() == 0 {
        return String::new();
    }
    
    // Convert string to vector for easier manipulation
    let mut chars: Vec<char> = Vec::new();
    let mut i: usize = 0;
    while i < a.len()
        invariant
            i <= a.len(),
            chars.len() == i,
            forall|j: int| 0 <= j < i ==> chars@[j] == a@[j],
            forall|j: int| 0 <= j < i ==> chars@[j] >= '0' && chars@[j] <= '9'
    {
        let char_at_i = a@[i as int];
        proof {
            assert(0 <= i < a.len());
            assert(a@[i as int] >= '0' && a@[i as int] <= '9');
        }
        chars.push(char_at_i);
        i += 1;
    }
    
    // Perform a simple "bad sort" - reverse sort (largest to smallest)
    // This is a basic bubble sort in reverse order
    let mut n = chars.len();
    while n > 1
        invariant
            chars.len() == a.len(),
            n <= chars.len(),
            forall|j: int| 0 <= j < chars.len() ==> chars@[j] >= '0' && chars@[j] <= '9'
        decreases n
    {
        let mut i: usize = 0;
        while i < n - 1
            invariant
                chars.len() == a.len(),
                i <= n - 1,
                n <= chars.len(),
                n > 0,
                forall|j: int| 0 <= j < chars.len() ==> chars@[j] >= '0' && chars@[j] <= '9'
            decreases n - 1 - i
        {
            // Sort in descending order (bad sort)
            if chars[i] < chars[i + 1] {
                let temp = chars[i];
                let next_char = chars[i + 1];
                chars.set(i, next_char);
                chars.set(i + 1, temp);
                
                proof {
                    assert(chars@[i as int] >= '0' && chars@[i as int] <= '9');
                    assert(chars@[(i + 1) as int] >= '0' && chars@[(i + 1) as int] <= '9');
                }
            }
            i += 1;
        }
        n -= 1;
    }
    
    // Convert back to string
    let mut result_chars: Vec<char> = Vec::new();
    let mut i: usize = 0;
    while i < chars.len()
        invariant
            i <= chars.len(),
            result_chars.len() == i,
            forall|j: int| 0 <= j < i ==> result_chars@[j] == chars@[j],
            forall|j: int| 0 <= j < chars.len() ==> chars@[j] >= '0' && chars@[j] <= '9',
            forall|j: int| 0 <= j < result_chars.len() ==> result_chars@[j] >= '0' && result_chars@[j] <= '9'
    {
        let char_val = chars[i];
        proof {
            assert(char_val >= '0' && char_val <= '9');
        }
        result_chars.push(char_val);
        i += 1;
    }
    
    // Convert Vec<char> to String
    let result = String::from_chars(result_chars);
    
    proof {
        assert(result.len() == a.len());
        assert(forall|i: int| 0 <= i < result.len() ==> result@[i] >= '0' && result@[i] <= '9');
    }
    
    result
}

}