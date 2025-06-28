use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn Reverse(a: Vec<char>) -> (b: Vec<char>)
    requires
        a.len() > 0
    ensures
        a.len() == b.len(),
        forall|k: int| 0 <= k < a.len() ==> b[k] == a[(a.len() as int - 1) - k]
{
    let mut result: Vec<char> = Vec::new();
    let mut i: usize = 0;
    
    while i < a.len()
        invariant
            i <= a.len(),
            result.len() == i,
            forall|k: int| 0 <= k < i ==> result[k] == a[(a.len() as int - 1) - k]
    {
        let idx = a.len() - 1 - i;
        result.push(a[idx]);
        i = i + 1;
    }
    
    result
}

}