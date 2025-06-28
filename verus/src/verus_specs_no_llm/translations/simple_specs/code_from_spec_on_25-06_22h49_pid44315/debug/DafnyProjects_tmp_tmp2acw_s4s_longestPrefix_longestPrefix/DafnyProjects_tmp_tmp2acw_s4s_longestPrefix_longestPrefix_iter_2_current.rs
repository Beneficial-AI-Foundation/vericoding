use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn longestPrefix(a: Vec<int>, b: &[int]) -> (i: usize)
    ensures
        i <= a.len() && i <= b.len(),
        a@.subrange(0, i as int) == b@.subrange(0, i as int),
        i < a.len() && i < b.len() ==> a[i] != b[i]
{
    let mut i: usize = 0;
    
    while i < a.len() && i < b.len()
        invariant
            i <= a.len() && i <= b.len(),
            a@.subrange(0, i as int) == b@.subrange(0, i as int),
        ensures
            i <= a.len() && i <= b.len(),
            a@.subrange(0, i as int) == b@.subrange(0, i as int),
            i < a.len() && i < b.len() ==> a[i] != b[i]
    {
        if a[i] == b[i] {
            i = i + 1;
        } else {
            break;
        }
    }
    
    i
}

}