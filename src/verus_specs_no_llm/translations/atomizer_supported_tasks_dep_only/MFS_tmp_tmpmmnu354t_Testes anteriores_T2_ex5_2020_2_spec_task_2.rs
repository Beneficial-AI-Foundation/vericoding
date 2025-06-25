// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn leq(a: Vec<int>, b: Vec<int>) -> (result: bool)
    ensures result <==> (a.len() <= b.len() and a[..] == b[..a.len()]) or (exists|k: int| 0 <= k < a.len() and k < b.len() and a[..k] == b[..k] and a[k] < b[k])
{
}

}