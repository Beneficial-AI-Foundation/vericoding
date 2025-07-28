use vstd::prelude::*;

fn main() {}

verus! {

fn extract_rear_chars(s: &Vec<Vec<u8>>) -> (result: Vec<u8>)
    requires
        forall|i: int| 0 <= i < s.len() ==> #[trigger] s[i].len() > 0,
    ensures
        s.len() == result.len(),
        forall|i: int| 0 <= i < s.len() ==> result[i] == #[trigger] s[i][s[i].len() - 1],
{
    let mut result = Vec::new();
    let mut i = 0;
    
    /* code modified by LLM (iteration 3): enhanced loop invariants to carry forward precondition about non-empty strings */
    while i < s.len()
        invariant
            i <= s.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result[j] == s[j][s[j].len() - 1],
            forall|k: int| 0 <= k < s.len() ==> s[k].len() > 0,
        decreases s.len() - i,
    {
        /* code modified by LLM (iteration 3): fixed type casting issue by casting to int properly */
        assert(0 <= i < s.len());
        assert((s[i].len() as int) > 0);
        let last_char = s[i][s[i].len() - 1];
        result.push(last_char);
        i += 1;
    }
    
    result
}

} // verus!