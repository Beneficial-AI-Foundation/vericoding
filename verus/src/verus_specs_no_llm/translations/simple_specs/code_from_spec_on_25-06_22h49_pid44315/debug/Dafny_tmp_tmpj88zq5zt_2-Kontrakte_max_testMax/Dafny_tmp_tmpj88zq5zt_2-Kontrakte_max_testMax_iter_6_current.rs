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
    let i_usize = i as usize;
    let j_usize = j as usize;
    
    if a[i_usize] > b[j_usize] {
        a[i_usize]
    } else {
        b[j_usize]
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