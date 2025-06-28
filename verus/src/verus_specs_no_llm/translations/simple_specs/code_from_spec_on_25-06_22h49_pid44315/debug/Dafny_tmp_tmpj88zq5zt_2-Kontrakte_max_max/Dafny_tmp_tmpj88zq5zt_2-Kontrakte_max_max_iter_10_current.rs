use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn max(a: Vec<int>, b: Vec<int>, i: int, j: int) -> (m: int)
    requires
        0 <= i < a.len(),
        0 <= j < b.len()
    ensures
        a.spec_index(i) > b.spec_index(j) ==> m == a.spec_index(i),
        a.spec_index(i) <= b.spec_index(j) ==> m == b.spec_index(j)
{
    let a_val = a[i as usize];
    let b_val = b[j as usize];
    
    // Establish the connection between executable and spec indexing
    assert(a.spec_index(i) == a_val);
    assert(b.spec_index(j) == b_val);
    
    if a_val > b_val {
        // When a_val > b_val, we know a.spec_index(i) > b.spec_index(j)
        assert(a.spec_index(i) > b.spec_index(j));
        a_val
    } else {
        // When a_val <= b_val, we know a.spec_index(i) <= b.spec_index(j)
        assert(a.spec_index(i) <= b.spec_index(j));
        b_val
    }
}

}