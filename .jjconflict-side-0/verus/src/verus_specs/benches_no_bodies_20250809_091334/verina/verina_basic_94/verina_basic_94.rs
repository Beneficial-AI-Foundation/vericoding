use vstd::prelude::*;

verus! {

spec fn iter_copy_precond(s: Seq<int>) -> bool {
    true
}

fn iter_copy(s: &Vec<int>) -> (result: Vec<int>)
    requires iter_copy_precond(s@),
    ensures 
        s@.len() == result@.len(),
        forall|i: int| 0 <= i < s@.len() ==> s@[i] == result@[i],
{
    return Vec::new();  // TODO: Remove this line and implement the function body
}

spec fn iter_copy_postcond(s: Seq<int>, result: Seq<int>) -> bool {
    s.len() == result.len() && 
    (forall|i: int| 0 <= i < s.len() ==> s[i] == result[i])
}

proof fn iter_copy_spec_satisfied(s: Seq<int>)
    requires iter_copy_precond(s),
    ensures exists|result: Seq<int>| iter_copy_postcond(s, result),
{
    assume(false);  // TODO: Remove this line and implement the proof
}

}

fn main() {}