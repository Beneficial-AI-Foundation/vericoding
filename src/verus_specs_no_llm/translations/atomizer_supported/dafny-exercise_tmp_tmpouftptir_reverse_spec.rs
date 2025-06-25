// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn Reverse(a: Vec<char>) -> (b: Vec<char>)
    requires a.len() > 0
    ensures a == old(a),
            b.len() == a.len(),
            forall|i: int| 0 <= i < a.len() ==> b[i] == a[a.len() - i - 1]
{
}

}