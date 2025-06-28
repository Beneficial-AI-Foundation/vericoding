// Translated from Dafny
use builtin::*;
use builtin_macros::*;

use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn ContainsZ(s: String) -> (result: bool)
    ensures
        result <==> (exists i :: 0 <= i < s.len() && (s.spec_index(i) == 'z' || s.spec_index(i) == 'Z'))
{
    return false;
}

}