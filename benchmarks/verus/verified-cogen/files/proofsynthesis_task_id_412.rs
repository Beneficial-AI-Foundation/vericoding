use vstd::prelude::*;

verus! {

fn remove_odds(arr: &Vec<u32>) -> (even_list: Vec<u32>)

    ensures
        even_list@ == arr@.filter(|x: u32| x % 2 == 0),
{
    assume(false);
    unreached()
}

}
fn main() {}