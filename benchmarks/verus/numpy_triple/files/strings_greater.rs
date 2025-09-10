use vstd::prelude::*;
use vstd::string::*;

verus! {

spec fn string_compare_gt(s1: Seq<char>, s2: Seq<char>) -> bool;

fn greater(x1: &Vec<String>, x2: &Vec<String>) -> (result: Vec<bool>)
    requires x1.len() == x2.len(),
    ensures 
        result.len() == x1.len(),

        forall|i: int| 0 <= i < result.len() ==> 
            result[i] == string_compare_gt(x1[i]@, x2[i]@),

        forall|i: int| 0 <= i < result.len() ==> 
            result[i] ==> !string_compare_gt(x2[i]@, x1[i]@),

        forall|i: int| 0 <= i < result.len() ==> 
            (x1[i]@ == x2[i]@) ==> (result[i] == false),
{
    assume(false);
    unreached()
}

}
fn main() {}