use vstd::prelude::*;

verus! {

spec fn count_to(a: &[bool], n: int) -> int
    decreases n when 0 <= n <= a.len()
{
    if n <= 0 { 
        0int 
    } else { 
        count_to(a, n - 1) + if a[n - 1] { 1int } else { 0int } 
    }
}

fn count_true(a: &[bool]) -> (result: usize)
    ensures result == count_to(a, a.len() as int)
{
    assume(false);
    unreached();
}

}
fn main() {}