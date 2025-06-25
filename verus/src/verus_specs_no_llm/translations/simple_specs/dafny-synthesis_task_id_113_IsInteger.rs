// Translated from Dafny
use builtin::*;
use builtin_macros::*;

use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn IsDigit(c: char) -> bool {
    48 <= c as int <= 57
}

fn IsInteger(s: String) -> (result: bool)
    ensures
        result <==> (s.len() > 0) && (forall i :: 0 <= i < s.len() ==> IsDigit(s.spec_index(i)))
{
    return false;
}

}