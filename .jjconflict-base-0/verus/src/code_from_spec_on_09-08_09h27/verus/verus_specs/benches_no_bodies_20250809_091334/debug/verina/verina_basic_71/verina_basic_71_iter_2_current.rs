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
    let mut result = Vec::new();
    let mut i = 0;
    
    /* code modified by LLM (iteration 1): added decreases clause to ensure loop termination */
    while i < str1.len() && i < str2.len()
        invariant 
            i <= str1.len(),
            i <= str2.len(),
            result.len() == i,
            result@ == str1@.subrange(0, i as int),
            result@ == str2@.subrange(0, i as int),
            forall|j: int| 0 <= j < i ==> str1@[j] == str2@[j]
        decreases str1.len().min(str2.len()) - i
    {
        if str1[i] == str2[i] {
            result.push(str1[i]);
            i += 1;
        } else {
            break;
        }
    }
    
    result
}

proof fn longest_common_prefix_spec_satisfied(str1: Seq<char>, str2: Seq<char>)
    requires longest_common_prefix_precond(str1, str2)
{
    // The precondition is trivially true, so there's nothing to prove here
    // The implementation above satisfies the postcondition by construction
}

}

fn main() {}