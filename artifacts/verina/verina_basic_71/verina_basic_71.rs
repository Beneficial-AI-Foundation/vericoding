use vstd::prelude::*;

verus! {

// Precondition predicate
spec fn longest_common_prefix_precond(str1: Seq<char>, str2: Seq<char>) -> bool {
    true
}

// Postcondition predicate
spec fn longest_common_prefix_postcond(
    str1: Seq<char>, 
    str2: Seq<char>, 
    result: Seq<char>
) -> bool {
    &&& result.len() <= str1.len()
    &&& result == str1.subrange(0, result.len() as int)
    &&& result.len() <= str2.len()
    &&& result == str2.subrange(0, result.len() as int)
    &&& (result.len() == str1.len() || result.len() == str2.len() || 
         (result.len() < str1.len() && result.len() < str2.len() && 
          str1[result.len() as int] != str2[result.len() as int]))
}

fn longest_common_prefix(str1: &Vec<char>, str2: &Vec<char>) -> (result: Vec<char>)
    requires longest_common_prefix_precond(str1@, str2@)
    ensures longest_common_prefix_postcond(str1@, str2@, result@)
{
    let min_length = if str1.len() < str2.len() { str1.len() } else { str2.len() };
    let mut result = Vec::new();
    let mut idx = 0;
    
    while idx < min_length && idx < str1.len() && idx < str2.len() && str1[idx] == str2[idx]
        invariant 
            idx <= min_length,
            min_length <= str1.len(),
            min_length <= str2.len(),
            result.len() == idx,
            idx <= str1.len(),
            idx <= str2.len(),
            result@ == str1@.subrange(0, idx as int),
            result@ == str2@.subrange(0, idx as int),
            forall|i: int| 0 <= i < idx ==> str1[i] == str2[i]
        decreases min_length - idx
    {
        result.push(str1[idx]);
        idx += 1;
    }
    
    result
}

proof fn longest_common_prefix_spec_satisfied(str1: Seq<char>, str2: Seq<char>)
    requires longest_common_prefix_precond(str1, str2)
{
    // Proof body omitted (corresponds to "sorry" in Lean)
}

}

fn main() {}