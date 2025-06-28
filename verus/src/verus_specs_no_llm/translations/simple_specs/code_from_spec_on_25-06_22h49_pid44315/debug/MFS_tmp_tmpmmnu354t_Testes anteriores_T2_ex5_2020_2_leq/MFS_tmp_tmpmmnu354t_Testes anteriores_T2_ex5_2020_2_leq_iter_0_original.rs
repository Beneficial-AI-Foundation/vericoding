// Translated from Dafny
use builtin::*;
use builtin_macros::*;

use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn leq(a: Vec<int>, b: Vec<int>) -> (result: bool)
    ensures
        result <==> (a.len() <= b.len() && a.spec_index(..) == b.spec_index(..a.len())) || (exists k :: 0 <= k < a.len() && k < b.len() && a.spec_index(..k) == b.spec_index(..k) && a.spec_index(k) < b.spec_index(k))
{
    return false;
}

}