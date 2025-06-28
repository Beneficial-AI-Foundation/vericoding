use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn arrayProduct(a: Vec<i32>, b: Vec<i32>) -> (c: Vec<i32>)
    requires
        a.len() == b.len()
    ensures
        c.len() == a.len(),
        forall |i: int| 0 <= i < a.len() ==> a.spec_index(i) * b.spec_index(i) == c.spec_index(i)
{
    let mut c = Vec::new();
    let mut i: usize = 0;
    
    while i < a.len()
        invariant
            i <= a.len(),
            c.len() == i,
            forall |j: int| 0 <= j < i ==> c.spec_index(j) == a.spec_index(j) * b.spec_index(j)
    {
        let product = a[i] * b[i];
        c.push(product);
        i = i + 1;
    }
    
    c
}

}