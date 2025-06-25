// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
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