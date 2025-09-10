use vstd::prelude::*;

verus! {

fn amax(a: Vec<i32>) -> (result: i32)
    requires a.len() > 0,
    ensures
        (exists|max_idx: int| 0 <= max_idx < a.len() &&
            result == a@[max_idx] &&
            (forall|i: int| 0 <= i < a.len() ==> a@[i] <= result)) &&
        (exists|first_max_idx: int| 0 <= first_max_idx < a.len() &&
            result == a@[first_max_idx] &&
            (forall|i: int| 0 <= i < a.len() && a@[i] == result ==> first_max_idx <= i) &&
            (forall|i: int| 0 <= i < a.len() ==> a@[i] <= result)) &&
        ((forall|i: int, j: int| 0 <= i < a.len() && 0 <= j < a.len() ==> a@[i] == a@[j]) ==> 
            result == a@[0]) &&
        (exists|witness: int| 0 <= witness < a.len() && result == a@[witness])
{
    assume(false);
    unreached()
}

}
fn main() {}