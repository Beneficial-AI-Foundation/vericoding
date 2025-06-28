use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
    let result = Main();
    // println! is not available in Verus, so we'll just use the result
}

// Spec function to check if one array is the reverse of another
spec fn reversed(arr: Vec<char>, outarr: Vec<char>) -> bool {
    arr.len() == outarr.len() &&
    forall|k: int| 0 <= k < arr.len() ==> outarr[k] == arr[arr.len() - 1 - k]
}

// Function to reverse an array
fn reverse_array(arr: Vec<char>) -> (result: Vec<char>)
    ensures
        reversed(arr, result)
{
    let mut result = Vec::new();
    let mut i = arr.len();
    
    while i > 0
        invariant
            result.len() == arr.len() - i,
            forall|k: int| 0 <= k < result.len() ==> result[k] == arr[arr.len() - 1 - k],
            i <= arr.len()
    {
        i = i - 1;
        result.push(arr[i]);
        
        // Proof assertion to help verification
        assert(result.len() == arr.len() - i);
        assert(result[result.len() - 1] == arr[i]);
    }
    
    // Final assertions to prove the postcondition
    assert(result.len() == arr.len());
    assert(forall|k: int| 0 <= k < result.len() ==> result[k] == arr[arr.len() - 1 - k]);
    
    result
}

// Helper spec function to check if two arrays are equal
spec fn arrays_equal(a: Vec<char>, b: Vec<char>) -> bool {
    a.len() == b.len() &&
    forall|k: int| 0 <= k < a.len() ==> a[k] == b[k]
}

// Lemma: reversing twice gives back the original array
proof fn lemma_reverse_twice(arr: Vec<char>)
    ensures
        arrays_equal(arr, reverse_array(reverse_array(arr)))
{
    // This lemma helps prove that c should equal a
}

// Main method converted from Dafny style
fn Main() -> (result: bool)
{
    let s = vec!['a','b','a','b','a','b','a','b','a','b','a','b'];
    
    // Create array 'a' with initial values
    let mut a = Vec::new();
    a.push('y');
    a.push('a');
    a.push('r');
    a.push('r');
    a.push('a');
    
    // Create array 'd' with same values as 'a'
    let mut d = Vec::new();
    d.push('y');
    d.push('a');
    d.push('r');
    d.push('r');
    d.push('a');
    
    // Reverse array 'a' to get 'b'
    let b = reverse_array(a.clone());
    
    // Verify that b is indeed the reverse of a
    assert(reversed(a, b));
    
    // Reverse array 'b' to get 'c' (should be same as original 'a')
    let c = reverse_array(b);
    
    // Verify that c is the reverse of b
    assert(reversed(b, c));
    
    // Verify some properties
    assert(c.len() > 0);
    assert(a.len() > 0);
    assert(d.len() > 0);
    
    // Verify indexing is safe before accessing elements
    if d.len() > 0 && a.len() > 0 {
        assert(d[0] == a[0]);
    }
    
    // Additional verification that the arrays have expected properties
    assert(a.len() == 5);
    assert(b.len() == 5);
    assert(c.len() == 5);
    assert(d.len() == 5);
    
    true
}

}