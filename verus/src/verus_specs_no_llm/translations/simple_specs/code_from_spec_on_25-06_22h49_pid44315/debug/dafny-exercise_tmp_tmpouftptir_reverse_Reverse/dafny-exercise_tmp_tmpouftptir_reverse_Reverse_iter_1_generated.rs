use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn Reverse(a: Vec<char>) -> (b: Vec<char>)
    requires
        a.len() > 0
    ensures
        a == old(a),
        b.len() == a.len(),
        forall|i: int| 0 <= i < a.len() ==> b.spec_index(i) == a.spec_index(a.len() - i - 1)
{
    let mut b = Vec::new();
    let mut j = a.len() - 1;
    
    while j < a.len()
        invariant
            b.len() + j + 1 == a.len(),
            j < a.len(),
            forall|k: int| 0 <= k < b.len() ==> b.spec_index(k) == a.spec_index(a.len() - 1 - k)
    {
        b.push(a[j]);
        if j == 0 {
            break;
        }
        j = j - 1;
    }
    
    b
}

}