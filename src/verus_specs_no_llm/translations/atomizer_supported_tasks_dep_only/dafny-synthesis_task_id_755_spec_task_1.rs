// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn SecondSmallest(s: Vec<int>) -> (secondSmallest: int)
    requires s.len() >= 2
    // There must be at least 2 different values, a minimum and another one,
             exists|i: int, j: int| 0 <= i < s.len() and 0 <= j < s.len() and i != j and s[i] == min(s[..]) and s[j] != s[i]
    ensures exists|i: int, j: int| 0 <= i < s.len() and 0 <= j < s.len() and i != j and s[i] == min(s[..]) and s[j] == secondSmallest,
            forall|k: int|  0 <= k < s.len() and s[k] != min(s[..])  ==>  s[k] >= secondSmallest
{
}

}