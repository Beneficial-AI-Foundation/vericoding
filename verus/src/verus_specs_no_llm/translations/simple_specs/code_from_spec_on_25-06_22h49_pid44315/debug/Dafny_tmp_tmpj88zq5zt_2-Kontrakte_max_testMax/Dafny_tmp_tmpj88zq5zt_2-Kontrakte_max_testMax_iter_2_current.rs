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
        a[i] > b[j] ==> m == a[i],
        a[i] <= b[j] ==> m == b[j]
{
    if a[i] > b[j] {
        a[i]
    } else {
        b[j]
    }
}

fn test_max(a: Vec<int>, b: Vec<int>, i: int, j: int) -> (result: (int, Vec<int>, int, int))
    requires
        0 <= i < a.len(),
        0 <= j < b.len()
    ensures
        a[i] > b[j] ==> result.0 == a[i],
        a[i] <= b[j] ==> result.0 == b[j]
{
    let m = max(&a, &b, i, j);
    (m, Vec::new(), 0, 0)
}

}