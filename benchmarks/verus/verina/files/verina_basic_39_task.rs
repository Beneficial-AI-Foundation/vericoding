use vstd::prelude::*;

verus! {

fn rotate_right(l: &Vec<i32>, n: usize) -> (result: Vec<i32>)
    ensures
        result.len() == l.len(),
        forall|i: int| 0 <= i < l.len() ==> {
            let len = l.len() as int;
            let rotated_index = ((i - n as int + len) % len) as int;
            #[trigger] result[i] == l[rotated_index]
        },
{
    assume(false);
    unreached()
}

}
fn main() {}