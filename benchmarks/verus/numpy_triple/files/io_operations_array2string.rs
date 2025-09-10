use vstd::prelude::*;

verus! {

fn array2string(arr: Vec<f32>, separator: &str) -> (result: Vec<char>)
    ensures
        result@.len() > 0,
        result@[0] == '[',
        result@[result@.len() - 1] == ']'
{
    assume(false);
    unreached()
}

}
fn main() {}