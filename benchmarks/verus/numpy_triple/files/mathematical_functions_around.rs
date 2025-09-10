use vstd::prelude::*;

verus! {

fn around(a: Vec<i32>, decimals: i32) -> (result: Vec<i32>)
    requires decimals == 0,
    ensures
        result.len() == a.len(),

        forall|i: int| 0 <= i < a.len() && a[i] == 0 ==> result[i] == 0,

        forall|i: int, j: int| 0 <= i < a.len() && 0 <= j < a.len() && a[i] <= a[j] ==> result[i] <= result[j],

        forall|i: int| 0 <= i < a.len() ==>
            result[i] - 1 <= a[i] && a[i] <= result[i] + 1,

        forall|i: int| 0 <= i < a.len() && a[i] >= 0 ==> result[i] >= 0,
{
    assume(false);
    unreached()
}

}
fn main() {}