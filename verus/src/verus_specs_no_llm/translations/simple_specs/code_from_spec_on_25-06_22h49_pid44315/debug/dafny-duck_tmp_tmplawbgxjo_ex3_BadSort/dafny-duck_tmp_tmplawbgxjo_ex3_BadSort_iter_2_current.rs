use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

// Helper function to convert char to int for comparison
spec fn char_to_int(c: char) -> int {
    c as int
}

// Helper function to create a string from a vector of characters
fn vec_to_string(v: Vec<char>) -> (result: String)
    ensures
        result.len() == v.len(),
        forall|i: int| 0 <= i < v.len() ==> result.spec_index(i) == v[i as nat]
{
    let mut s = String::new();
    let mut idx = 0;
    while idx < v.len()
        invariant
            idx <= v.len(),
            s.len() == idx,
            forall|i: int| 0 <= i < idx ==> s.spec_index(i) == v[i as nat]
    {
        s.push(v[idx]);
        idx += 1;
    }
    s
}

fn BadSort(a: String) -> (b: String)
    requires
        forall|i: int| 0 <= i < a.len() ==> a.spec_index(i) >= '0' && a.spec_index(i) <= '9'
    ensures
        b.len() == a.len(),
        forall|i: int| 0 <= i < a.len() ==> b.spec_index(i) >= '0' && b.spec_index(i) <= '9'
{
    if a.len() == 0 {
        return String::new();
    }
    
    // Convert string to vector for easier manipulation
    let mut chars: Vec<char> = Vec::new();
    let mut i = 0;
    while i < a.len()
        invariant
            i <= a.len(),
            chars.len() == i,
            forall|j: int| 0 <= j < i ==> chars[j as nat] == a.spec_index(j),
            forall|j: int| 0 <= j < i ==> chars[j as nat] >= '0' && chars[j as nat] <= '9'
    {
        chars.push(a.spec_index(i as int));
        i += 1;
    }
    
    // Perform a simple "bad sort" - reverse sort (largest to smallest)
    // This is a basic bubble sort in reverse order
    let mut n = chars.len();
    while n > 1
        invariant
            chars.len() == a.len(),
            forall|j: int| 0 <= j < chars.len() ==> chars[j as nat] >= '0' && chars[j as nat] <= '9'
    {
        let mut i = 0;
        while i < n - 1
            invariant
                chars.len() == a.len(),
                i <= n - 1,
                n <= chars.len(),
                forall|j: int| 0 <= j < chars.len() ==> chars[j as nat] >= '0' && chars[j as nat] <= '9'
        {
            // Sort in descending order (bad sort)
            if chars[i] < chars[i + 1] {
                let temp = chars[i];
                chars.set(i, chars[i + 1]);
                chars.set(i + 1, temp);
            }
            i += 1;
        }
        n -= 1;
    }
    
    // Convert back to string
    vec_to_string(chars)
}

}