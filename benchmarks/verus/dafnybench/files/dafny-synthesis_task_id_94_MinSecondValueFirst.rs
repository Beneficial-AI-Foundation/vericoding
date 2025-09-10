use vstd::prelude::*;

verus! {

fn min_second_value_first(s: &Vec<Vec<i32>>) -> (first_of_min_second: i32)
    requires 
        s.len() > 0,
        forall|i: int| 0 <= i < s.len() ==> s@[i].len() >= 2,
    ensures 
        exists|i: int| 0 <= i < s.len() && first_of_min_second == s@[i]@[0] && 
            (forall|j: int| 0 <= j < s.len() ==> s@[i]@[1] <= s@[j]@[1]),
{
    assume(false);
    unreached();
}

}
fn main() {}