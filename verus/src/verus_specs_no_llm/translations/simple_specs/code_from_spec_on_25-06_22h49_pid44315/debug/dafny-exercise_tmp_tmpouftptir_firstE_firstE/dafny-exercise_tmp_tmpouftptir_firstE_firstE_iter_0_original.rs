// Translated from Dafny
use builtin::*;
use builtin_macros::*;

use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn firstE(a: Vec<char>) -> (x: int)
    ensures
        if 'e' in a.spec_index(..) then 0 <= x < a.len() && a.spec_index(x) == 'e' && forall i | 0 <= i < x :: a.spec_index(i) != 'e' else x == -1
{
    return 0;
}

}