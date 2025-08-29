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
    let mut acc = Vec::new();
    let mut i = 0;
    
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            acc@.len() == i,
            forall|j: int| 0 <= j < i ==> s@[j] == acc@[j],
        decreases s.len() - i,
    {
        acc.push(s[i]);
        i += 1;
    }
    
    acc
}

spec fn iter_copy_postcond(s: Seq<int>, result: Seq<int>) -> bool {
    s.len() == result.len() && 
    (forall|i: int| 0 <= i < s.len() ==> s[i] == result[i])
}

proof fn iter_copy_spec_satisfied(s: Seq<int>)
    requires iter_copy_precond(s),
    ensures exists|result: Seq<int>| iter_copy_postcond(s, result),
{
    // The witness is s itself - copying s gives us s
    assert(iter_copy_postcond(s, s));
}

}

fn main() {}