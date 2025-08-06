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
    return Vec::new();  // TODO: Remove this line and implement the function body
}

} // verus!
