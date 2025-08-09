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
    return Vec::new();  // TODO: Remove this line and implement the function body
}

} // verus!

fn main() {}
