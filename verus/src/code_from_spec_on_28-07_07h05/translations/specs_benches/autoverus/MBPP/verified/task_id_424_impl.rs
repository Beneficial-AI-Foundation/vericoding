use vstd::prelude::*;

fn main() {
    // TODO: Remove this comment and implement the function body
}

verus! {

//IMPL extract_rear_chars
fn extract_rear_chars(s: &Vec<Vec<u8>>) -> (result: Vec<u8>)
    requires
        forall|i: int| 0 <= i < s.len() ==> #[trigger] s[i].len() > 0,
    ensures
        s.len() == result.len(),
        forall|i: int| 0 <= i < s.len() ==> result[i] == #[trigger] s[i][s[i].len() - 1],
{
    let mut result = Vec::new();
    let mut i = 0;
    
    /* code modified by LLM (iteration 1): added bounds checks and proper invariants to handle arithmetic overflow and precondition failures */
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result[j] == s[j][s[j].len() - 1],
            forall|j: int| 0 <= j < s.len() ==> s[j].len() > 0,
        decreases s.len() - i,
    {
        /* code modified by LLM (iteration 1): added assertion to help verification prove preconditions */
        assert(i < s.len());
        assert(s[i as int].len() > 0);
        assert(s[i as int].len() - 1 < s[i as int].len());
        
        let last_char = s[i][s[i].len() - 1];
        result.push(last_char);
        i += 1;
    }
    
    result
}

} // verus!