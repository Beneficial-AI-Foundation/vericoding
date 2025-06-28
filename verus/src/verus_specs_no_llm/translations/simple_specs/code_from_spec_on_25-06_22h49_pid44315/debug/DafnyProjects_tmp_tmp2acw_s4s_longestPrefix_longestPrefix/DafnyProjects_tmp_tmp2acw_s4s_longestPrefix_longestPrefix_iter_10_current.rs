use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn longestPrefix(a: &[int], b: &[int]) -> (i: usize)
    ensures
        i <= a.len() && i <= b.len(),
        a@.subrange(0, i as int) == b@.subrange(0, i as int),
        i < a.len() && i < b.len() ==> a[i] != b[i]
{
    let mut i: usize = 0;
    
    while i < a.len() && i < b.len() && a[i] == b[i]
        invariant
            i <= a.len() && i <= b.len(),
            a@.subrange(0, i as int) == b@.subrange(0, i as int),
    {
        i = i + 1;
    }
    
    i
}

}