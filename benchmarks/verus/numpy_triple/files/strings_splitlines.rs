use vstd::prelude::*;

verus! {

fn splitlines(a: Vec<String>, keepends: bool) -> (result: Vec<Vec<String>>)
    requires a.len() > 0,
    ensures 
        result.len() == a.len(),
        forall|i: int| 0 <= i < result.len() ==> #[trigger] result[i].len() >= 1
{
    assume(false);
    unreached()
}

}
fn main() {}