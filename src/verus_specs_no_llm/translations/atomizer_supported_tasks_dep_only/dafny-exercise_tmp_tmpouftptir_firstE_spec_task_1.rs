// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn firstE(a: Vec<char>) -> (x: int)
    ensures if 'e' in a[..] then 0 <= x < a.len() and a[x] == 'e' and forall|i | 0 <= i < x: int| a[i] != 'e' else x == -1
{
}

}