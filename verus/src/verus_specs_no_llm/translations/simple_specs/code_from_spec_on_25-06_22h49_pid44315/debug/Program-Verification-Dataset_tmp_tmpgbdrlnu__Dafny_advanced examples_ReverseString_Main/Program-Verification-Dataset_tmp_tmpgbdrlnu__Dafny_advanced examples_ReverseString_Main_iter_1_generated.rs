use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
    let result = Main();
    println!("Result: {}", result);
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
            forall|k: int| 0 <= k < result.len() ==> result[k] == arr[arr.len() - 1 - k]
    {
        i = i - 1;
        result.push(arr[i]);
    }
    
    result
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
    
    // Reverse array 'b' to get 'c' (should be same as original 'a')
    let c = reverse_array(b);
    
    // Verify some properties
    assert(c.len() > 0);
    assert(d[0] == a[0]);
    
    true
}

}