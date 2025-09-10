use vstd::prelude::*;

verus! {

fn fromstring(input: Vec<char>, sep: Vec<char>) -> (result: Vec<f32>)
    requires
        sep.len() > 0,
        input.len() > 0,
    ensures
        result.len() > 0,
{
    assume(false);
    unreached();
}

}
fn main() {}