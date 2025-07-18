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
    
    assert(a_val == a.spec_index(i));
    assert(b_val == b.spec_index(j));
    
    if a_val > b_val {
        assert(a.spec_index(i) > b.spec_index(j));
        a_val
    } else {
        assert(a.spec_index(i) <= b.spec_index(j));
        b_val
    }
}

}