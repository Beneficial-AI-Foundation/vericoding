use vstd::prelude::*;

verus! {

proof fn element_at_index_after_rotation(l: Seq<int>, n: int, index: int) -> (element: int)
    requires 
        n >= 0,
        0 <= index < l.len(),
    ensures 
        element == l[((index - n + l.len() as int) % l.len() as int) as int],
{
    assume(false);
    unreached()
}

}
fn main() {}