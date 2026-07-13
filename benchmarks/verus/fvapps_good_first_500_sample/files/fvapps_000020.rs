// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
type CustomerInfo = Seq<(u32, i32, i32)>;

spec fn customer_info_time_monotonic(info: CustomerInfo) -> bool {
    forall|i: int, j: int| 0 <= i < j < info.len() ==> info[i].0 <= info[j].0
}

spec fn customer_satisfiable(initial_temp: i32, customer: (u32, i32, i32)) -> bool {
    let (t, l, h) = customer;
    let temp_range_low = initial_temp - (t as i32);
    let temp_range_high = initial_temp + (t as i32);
    !(h < temp_range_low || temp_range_high < l)
}

fn check_restaurant_temps(initial_temp: i32, customer_info: Vec<(u32, i32, i32)>) -> (result: bool)
    requires customer_info_time_monotonic(customer_info@),
    ensures 
        customer_info@.len() == 0 ==> result == true,
        customer_info@.len() == 1 ==> 
            (customer_satisfiable(initial_temp, customer_info@[0]) <==> result == true)
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume(false);
    false
    // impl-end
}
// </vc-code>


}
fn main() {
    // let result1 = check_restaurant_temps(0, vec![(5, 1, 2), (7, 3, 5), (10, -1, 0)]);
    // println!("{}", if result1 { "YES" } else { "NO" }); // Should be "YES"
    
    // let result2 = check_restaurant_temps(12, vec![(5, 7, 10), (10, 16, 20)]);
    // println!("{}", if result2 { "YES" } else { "NO" }); // Should be "NO"
    
    // let result3 = check_restaurant_temps(-100, vec![(100, 0, 0), (100, -50, 50), (200, 100, 100)]);
    // println!("{}", if result3 { "YES" } else { "NO" }); // Should be "YES"
}