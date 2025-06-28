// Translated from Dafny
use builtin::*;
use builtin_macros::*;

use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn Match(s: String, p: String) -> (b: bool)
    requires
        s.len() == p.len()
    ensures
        b <==> forall n :: 0 <= n < s.len() ==> s.spec_index(n) == p.spec_index(n) || p.spec_index(n) == '?'
{
    return false;
}

}