// Translated from Dafny
use builtin::*;
use builtin_macros::*;

use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn firste(a: Vec<char>) -> (c: int)
    ensures
        -1 <= c < a.len(),
        0 <= c < a.len() ==> a.spec_index(c) == 'e' && forall x :: 0 <= x < c ==> a.spec_index(x) != 'e',
        c == -1 ==> forall x :: 0 <= x < a.len() ==> a.spec_index(x) != 'e'
{
    let mut i: usize = 0;
    
    while i < a.len()
        invariant
            i <= a.len(),
            forall x :: 0 <= x < i ==> a.spec_index(x) != 'e'
    {
        if a[i] == 'e' {
            return i as int;
        }
        i = i + 1;
    }
    
    return -1;
}

}