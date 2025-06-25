// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn ContainsConsecutiveNumbers(a: Vec<int>) -> (result: bool)
    requires a.len()>0
    ensures result <==> (exists|i: int| 0 <= i < a.len() - 1 and a[i] + 1 == a[i + 1])
{
}

}