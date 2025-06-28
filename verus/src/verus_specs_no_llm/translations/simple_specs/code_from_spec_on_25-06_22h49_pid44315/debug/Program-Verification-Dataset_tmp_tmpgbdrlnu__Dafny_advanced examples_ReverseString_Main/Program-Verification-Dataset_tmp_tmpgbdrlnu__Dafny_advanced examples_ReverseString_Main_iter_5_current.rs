use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
    let result = Main();
}

// Spec function to check if one array is the reverse of another
spec fn reversed(arr: Vec<char>, outarr: Vec<char>) -> bool {
    arr.len() == outarr.len() &&
    forall|k: nat| k < arr.len() ==> outarr[k as int] == arr[(arr.len() - 1 - k) as int]
}

// Function to reverse an array
fn reverse_array(arr: Vec<char>) -> (result: Vec<char>)
    ensures
        reversed(arr, result)
{
    let mut result = Vec::new();
    let mut i: usize = 0;
    
    while i < arr.len()
        invariant
            i <= arr.len(),
            result.len() == i,
            forall|k: nat| k < i ==> result[k as int] == arr[(arr.len() - 1 - k) as int]
    {
        result.push(arr[arr.len() - 1 - i]);
        i = i + 1;
    }
    
    result
}

// Helper spec function to check if two arrays are equal
spec fn arrays_equal(a: Vec<char>, b: Vec<char>) -> bool {
    a.len() == b.len() &&
    forall|k: nat| k < a.len() ==> a[k as int] == b[k as int]
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

// Helper function to create test vector
fn create_test_vec() -> (result: Vec<char>)
    ensures result.len() == 12
{
    let mut v = Vec::new();
    let mut i = 0;
    while i < 12
        invariant v.len() == i, i <= 12
    {
        if i % 2 == 0 {
            v.push('a');
        } else {
            v.push('b');
        }
        i = i + 1;
    }
    v
}

// Proof function to establish that reversing twice gives back original
proof fn prove_reverse_twice_property(arr: Vec<char>)
    requires arr.len() > 0
    ensures
        ({
            let rev1 = reverse_array(arr);
            let rev2 = reverse_array(rev1);
            arrays_equal(arr, rev2)
        })
{
    let rev1 = reverse_array(arr);
    let rev2 = reverse_array(rev1);
    
    assert forall|k: nat| k < arr.len() implies rev2[k as int] == arr[k as int] by {
        // rev1[k] == arr[arr.len() - 1 - k] (from first reverse)
        // rev2[k] == rev1[rev1.len() - 1 - k] (from second reverse)
        // Since rev1.len() == arr.len(), we have:
        // rev2[k] == rev1[arr.len() - 1 - k] == arr[arr.len() - 1 - (arr.len() - 1 - k)] == arr[k]
        let idx1 = (arr.len() - 1 - k) as int;
        let idx2 = (rev1.len() - 1 - k) as int;
        assert(rev1.len() == arr.len());
        assert(idx2 == idx1);
        assert(rev1[idx1] == arr[k as int]);
        assert(rev2[k as int] == rev1[idx2]);
        assert(rev2[k as int] == arr[k as int]);
    }
}

// Main method
fn Main() -> (result: bool)
{
    let s = create_test_vec();
    
    // Create array 'a' with initial values
    let a = create_yarra_vec();
    
    // Create array 'd' with same values as 'a'
    let d = create_yarra_vec();
    
    // Reverse array 'a' to get 'b'
    let b = reverse_array(a);
    
    // Reverse array 'b' to get 'c' (should be same as original 'a')
    let c = reverse_array(b);
    
    // Verify some basic properties
    assert(c.len() > 0);
    assert(a.len() > 0);
    assert(d.len() > 0);
    
    // Verify that the arrays have expected properties
    assert(a.len() == 5);
    assert(b.len() == 5);
    assert(c.len() == 5);
    assert(d.len() == 5);
    
    // Verify indexing is safe before accessing elements
    assert(d[0] == a[0]);
    
    // Use proof to establish the reverse twice property
    proof {
        prove_reverse_twice_property(a);
    }
    
    // Now we can assert that reversing twice gives back the original
    assert(arrays_equal(a, c));
    
    true
}

}