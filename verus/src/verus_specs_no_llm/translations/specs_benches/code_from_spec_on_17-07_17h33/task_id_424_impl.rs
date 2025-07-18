use vstd::prelude::*;

verus! {

//IMPL extract_rear_chars
/* code modified by LLM (iteration 3): Fixed function signature and specification placement */
fn extract_rear_chars(s: &Vec<Vec<char>>) -> (result: Vec<char>)
{
    return false;  // TODO: Remove this line and implement the function body
}
    // pre-conditions-start
    requires
        forall|i: int| 0 <= i < s.len() ==> #[trigger] s[i].len() > 0,
    // pre-conditions-end
    // post-conditions-start
    ensures
        s.len() == result.len(),
        forall|i: int| 0 <= i < s.len() ==> result[i] == #[trigger] s[i][s[i].len() - 1],
    // post-conditions-end
{
    /* code modified by LLM (iteration 3): Implemented function body with proper loop and invariants */
    let mut result = Vec::new();
    let mut i = 0;
    
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result[j] == s[j][s[j].len() - 1],
    {
        let last_char = s[i][s[i].len() - 1];
        result.push(last_char);
        i += 1;
    }
    
    result
}

} // verus!

fn main() {}