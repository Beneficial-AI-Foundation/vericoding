// Translated from Dafny
use builtin::*;
use builtin_macros::*;

use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn mCountMin(v: Vec<int>) -> (c: int)
    requires
        v.len()>0
    ensures
        c==countMin(v,min(v,v.len()),v.len())
//Implement && verify an O(v.len()) algorithm
{
    return 0;
}

}