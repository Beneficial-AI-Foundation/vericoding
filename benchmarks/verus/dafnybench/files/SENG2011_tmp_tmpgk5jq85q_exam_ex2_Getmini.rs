use vstd::prelude::*;

verus! {

fn get_mini(a: &[i32]) -> (mini: usize)
    requires a.len() > 0,
    ensures 
        0 <= mini < a.len(),
        forall|x: usize| 0 <= x < a.len() ==> a[mini as int] <= a[x as int],
        forall|x: usize| 0 <= x < mini ==> a[mini as int] < a[x as int],
{
    assume(false);
    unreached();
}

}
fn main() {}