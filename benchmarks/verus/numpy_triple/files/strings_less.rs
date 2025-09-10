use vstd::prelude::*;
use vstd::string::*;

verus! {

spec fn str_less_than(s1: String, s2: String) -> bool;

fn less(x1: Vec<String>, x2: Vec<String>) -> (result: Vec<bool>)
    requires x1.len() == x2.len(),
    ensures 
        result.len() == x1.len(),

        forall|i: int| 0 <= i < result.len() ==> result[i] == str_less_than(x1[i], x2[i]),

        forall|i: int| 0 <= i < result.len() && result[i] == true ==> !str_less_than(x2[i], x1[i]),

        forall|i: int| 0 <= i < result.len() && x1[i] == x2[i] ==> result[i] == false,

        forall|i: int| 0 <= i < result.len() ==> result[i] == true || result[i] == false,

        forall|i: int| 0 <= i < result.len() && result[i] == true ==> x1[i] != x2[i],

        forall|i: int| 0 <= i < result.len() ==> result[i] == true || x1[i] == x2[i] || str_less_than(x2[i], x1[i])
{
    assume(false);
    unreached()
}

}
fn main() {}