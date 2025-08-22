use vstd::prelude::*;

verus! {

fn extract_rear_chars(s: &Vec<Vec<char>>) -> (result: Vec<char>)
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
    let mut result = Vec::new();
    let mut i = 0;
    
    /* code modified by LLM (iteration 1): added decreases clause to prove loop termination */
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result[j] == s[j][s[j].len() - 1],
            forall|k: int| 0 <= k < s.len() ==> s[k].len() > 0,
        decreases s.len() - i
    {
        let last_char = s[i][s[i].len() - 1];
        result.push(last_char);
        i += 1;
    }
    
    result
}

} // verus!

fn main() {}