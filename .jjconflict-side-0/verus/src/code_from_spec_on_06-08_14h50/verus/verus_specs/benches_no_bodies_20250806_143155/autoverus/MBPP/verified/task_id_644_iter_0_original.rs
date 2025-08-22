use vstd::prelude::*;
fn main() {
    // TODO: Remove this comment and implement the function body
}

verus! {

fn reverse_to_k(list: &Vec<i32>, n: usize) -> (reversed_list: Vec<i32>)
    requires
        list@.len() > 0,
        0 < n < list@.len(),
    ensures
        reversed_list@ == list@.subrange(0, n as int).reverse().add(
            list@.subrange(n as int, list.len() as int),
        ),
{
    return Vec::new();  // TODO: Remove this line and implement the function body
}

} // verus!
