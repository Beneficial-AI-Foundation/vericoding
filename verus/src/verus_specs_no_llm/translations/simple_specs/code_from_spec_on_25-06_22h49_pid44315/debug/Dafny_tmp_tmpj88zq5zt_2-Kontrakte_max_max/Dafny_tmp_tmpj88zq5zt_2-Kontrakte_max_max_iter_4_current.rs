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
    
    if a_val > b_val {
        a_val
    } else {
        b_val
    }
}

}