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

fn ContainsConsecutiveNumbers(a: Vec<int>) -> (result: bool)
    requires
        a.len()>0
    ensures
        result <==> (exists i :: 0 <= i < a.len() - 1 && a.spec_index(i) + 1 == a.spec_index(i + 1))
{
    return false;
}

}