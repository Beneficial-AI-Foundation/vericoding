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
    forall|k: int| 0 <= k < arr.len() ==> outarr[k as int] == arr[arr.len() - 1 - k]
}

// Function to reverse an array
fn reverse_array(arr: Vec<char>) -> (result: Vec<char>)
    ensures
        reversed(arr, result)
{
    let ghost original_arr = arr;
    let mut result = Vec::new();
    let mut i = arr.len();
    
    while i > 0
        invariant
            result.len() == arr.len() - i,
            forall|k: int| 0 <= k < result.len() ==> result[k as int] == arr[arr.len() - 1 - k],
            i <= arr.len(),
            arr == original_arr
    {
        i = i - 1;
        result.push(arr[i]);
        
        // Proof assertions to help verification
        assert(result.len() == arr.len() - i);
        assert(result[result.len() - 1] == arr[i]);
        assert(forall|k: int| 0 <= k < result.len() - 1 ==> result[k as int] == arr[arr.len() - 1 - k]);
    }
    
    // Final assertions to prove the postcondition
    assert(result.len() == arr.len());
    assert(i == 0);
    assert(forall|k: int| 0 <= k < result.len() ==> result[k as int] == arr[arr.len() - 1 - k]);
    
    result
}

// Helper spec function to check if two arrays are equal
spec fn arrays_equal(a: Vec<char>, b: Vec<char>) -> bool {
    a.len() == b.len() &&
    forall|k: int| 0 <= k < a.len() ==> a[k as int] == b[k as int]
}

// Lemma: reversing twice gives back the original array
proof fn lemma_reverse_twice(arr: Vec<char>)
    ensures
        arrays_equal(arr, reverse_array(reverse_array(arr)))
{
    let rev1 = reverse_array(arr);
    let rev2 = reverse_array(rev1);
    
    // Prove that rev2 equals arr
    assert(arr.len() == rev2.len());
    assert(forall|k: int| 0 <= k < arr.len() ==> {
        let orig_idx = k;
        let rev1_idx = arr.len() - 1 - k;
        let rev2_idx = k;
        rev2[rev2_idx] == rev1[rev1.len() - 1 - rev2_idx] &&
        rev1[rev1_idx] == arr[arr.len() - 1 - rev1_idx] &&
        arr.len() - 1 - rev1_idx == orig_idx
    });
}

// Helper function to create a vector with initial values
fn create_yarra_vec() -> (result: Vec<char>)
    ensures result.len() == 5,
            result[0] == 'y',
            result[1] == 'a', 
            result[2] == 'r',
            result[3] == 'r',
            result[4] == 'a'
{
    let mut v = Vec::new();
    v.push('y');
    v.push('a');
    v.push('r');
    v.push('r');
    v.push('a');
    v
}

// Main method converted from Dafny style
fn Main() -> (result: bool)
{
    let s = vec!['a','b','a','b','a','b','a','b','a','b','a','b'];
    
    // Create array 'a' with initial values
    let a = create_yarra_vec();
    
    // Create array 'd' with same values as 'a'
    let d = create_yarra_vec();
    
    // Reverse array 'a' to get 'b'
    let b = reverse_array(a);
    
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
    assert(d.len() > 0 && a.len() > 0);
    assert(d[0] == a[0]);
    
    // Additional verification that the arrays have expected properties
    assert(a.len() == 5);
    assert(b.len() == 5);
    assert(c.len() == 5);
    assert(d.len() == 5);
    
    // Verify that reversing twice gives back the original
    assert(arrays_equal(a, c));
    
    true
}

}