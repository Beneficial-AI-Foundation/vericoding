use vstd::prelude::*;

verus! {

// <vc-helpers>
proof fn add_overflow_check(x: int, y: int) 
    ensures 
        (x + y >= i32::MIN as int && x + y <= i32::MAX as int) ==>
            (x + y) as i32 == (x as i32).checked_add(y as i32).unwrap()
{
    if x + y >= i32::MIN as int && x + y <= i32::MAX as int {
        assert((x as i32).checked_add(y as i32).is_some());
        let sum_i32 = (x as i32).checked_add(y as i32).unwrap();
        assert(sum_i32 as int == x + y);
        assert(sum_i32 == (x + y) as i32);
    }
}
// </vc-helpers>

// <vc-spec>
fn add(x: i32, y: i32) -> (res: Option<i32>)
    // post-conditions-start
    ensures
        res.is_some() ==> res.unwrap() == x + y,
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    if let Some(sum) = x.checked_add(y) {
        proof {
            add_overflow_check(x as int, y as int);
        }
        assert(sum == x + y);
        Some(sum)
    } else {
        None
    }
}
// </vc-code>

fn main() {}
}