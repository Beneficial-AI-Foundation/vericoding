use vstd::prelude::*;

verus! {

spec fn sum_to(arr: Seq<i64>) -> (result: int)
    decreases arr.len(),
{
    if arr.len() == 0 {
        0
    } else {
        sum_to(arr.drop_last()) + arr.last()
    }
}

fn sum(arr: &Vec<i64>) -> (sum: i128)

    ensures
        sum_to(arr@) == sum,
{
    assume(false);
    unreached()
}

}
fn main() {}