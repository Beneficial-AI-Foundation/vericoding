use vstd::prelude::*;

verus! {
    fn double_array_elements(s: &mut Vec<i32>)
        requires forall|i: int| 0 <= i < old(s).len() ==> #[trigger] old(s)[i] >= -1073741824 && old(s)[i] <= 1073741823, // prevent overflow
        ensures 
            forall|i: int| 0 <= i < old(s).len() ==> #[trigger] s[i] == 2 * old(s)[i],
            s.len() == old(s).len(),
    {
    // TODO: Remove this comment and implement the function body
    }
}

fn main() {}