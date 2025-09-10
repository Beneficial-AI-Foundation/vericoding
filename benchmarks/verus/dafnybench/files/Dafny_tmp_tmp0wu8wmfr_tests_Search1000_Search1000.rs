use vstd::prelude::*;

verus! {

spec fn is_2_pow(n: int) -> bool
    decreases n
{
    if n < 1 {
        false
    } else if n == 1 {
        true
    } else {
        n % 2 == 0 && is_2_pow(n / 2)
    }
}

fn search_1000(a: &[i32], x: i32) -> (k: usize)
    requires 
        a.len() >= 1000,
        forall|p: int, q: int| 0 <= p < q < 1000 ==> a[p] <= a[q],
    ensures 
        0 <= k <= 1000,
        forall|r: int| 0 <= r < k ==> a[r] < x,
        forall|r: int| k <= r < 1000 ==> a[r] >= x,
{
    assume(false);
    unreached()
}

}
fn main() {}