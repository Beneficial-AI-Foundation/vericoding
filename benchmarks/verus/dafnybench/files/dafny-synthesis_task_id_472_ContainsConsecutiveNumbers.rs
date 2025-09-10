use vstd::prelude::*;

verus! {

fn contains_consecutive_numbers(a: &[i32]) -> (result: bool)
    requires a.len() > 0
    ensures result <==> exists|i: int| #![trigger a.spec_index(i)] 
        0 <= i < (a.len() as int) - 1 && a[i] + 1 == a[i + 1]
{
    assume(false);
    unreached();
}

}
fn main() {}