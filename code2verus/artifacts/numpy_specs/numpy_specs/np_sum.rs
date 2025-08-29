use vstd::prelude::*;

verus! {

// ATOM
spec fn sum_array(a: Seq<i32>, start: int, end: int) -> int
    recommends 0 <= start <= end <= a.len()
    decreases end - start when 0 <= start < end
{
    if start == end { 
        0 
    } else { 
        a[start] as int + sum_array(a, start + 1, end) 
    }
}

// SPEC
fn sum(a: &Vec<i32>) -> (res: i32)
    ensures res as int == sum_array(a@, 0, a@.len() as int)
{
    // Empty method body as in original Dafny
    assume(false);
    0
}

}

fn main() {}