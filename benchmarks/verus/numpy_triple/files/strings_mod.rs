use vstd::prelude::*;

verus! {

fn mod_func(a: Vec<String>, values: Vec<String>) -> (result: Vec<String>)
    requires a.len() == values.len(),
    ensures 
        result.len() == a.len(),
{
    assume(false);
    unreached();
}

}
fn main() {}