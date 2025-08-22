use vstd::prelude::*;

verus! {
    fn append(a: &[int], b: int) -> (c: Vec<int>)
        requires a.len() < usize::MAX
        ensures c@ == a@ + seq![b]
    {
    return Vec::new();  // TODO: Remove this line and implement the function body
    }
}

fn main() {}