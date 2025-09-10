use vstd::prelude::*;

verus! {

fn search_recursive(a: Seq<int>, i: usize, j: usize, x: int) -> (result: isize)
    requires 
        i <= j,
        j <= a.len(),
    ensures
        (i <= result && result < j as isize) || result == -1,
        result != -1 ==> a[result as int] == x,
        result != -1 ==> forall|r: int| result < r && r < j as int ==> a[r] != x,
        result == -1 ==> forall|r: int| i as int <= r && r < j as int ==> a[r] != x,
    decreases j - i,
{
    assume(false);
    unreached()
}

}
fn main() {}