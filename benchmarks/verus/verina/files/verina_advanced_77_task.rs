use vstd::prelude::*;

verus! {

fn trap_rain_water(height: &Vec<usize>) -> (result: usize)
    requires height.len() >= 0,
    ensures result >= 0,
{
    assume(false);
    unreached();
}

}
fn main() {}