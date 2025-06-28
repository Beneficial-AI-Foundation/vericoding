use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn max(a: &Vec<int>, b: &Vec<int>, i: int, j: int) -> (m: int)
    requires 
        0 <= i < a.len(),
        0 <= j < b.len()
    ensures 
        a@[i] > b@[j] ==> m == a@[i],
        a@[i] <= b@[j] ==> m == b@[j]
{
    // Convert int to usize with proof that conversion is valid
    let i_usize = i as usize;
    let j_usize = j as usize;
    
    // Proof that the conversion is valid and within bounds
    proof {
        assert(0 <= i < a.len());
        assert(0 <= j < b.len());
        assert(i_usize == i);
        assert(j_usize == j);
        assert(i_usize < a.len());
        assert(j_usize < b.len());
    }
    
    // Access vector elements
    let a_val = a[i_usize];
    let b_val = b[j_usize];
    
    // Compare and return the maximum
    if a_val > b_val {
        a_val
    } else {
        b_val
    }
}

fn test_max(a: &Vec<int>, b: &Vec<int>, i: int, j: int) -> (result: (int, Vec<int>, int, int))
    requires
        0 <= i < a.len(),
        0 <= j < b.len()
    ensures
        a@[i] > b@[j] ==> result.0 == a@[i],
        a@[i] <= b@[j] ==> result.0 == b@[j]
{
    let m = max(a, b, i, j);
    (m, Vec::new(), 0, 0)
}

}