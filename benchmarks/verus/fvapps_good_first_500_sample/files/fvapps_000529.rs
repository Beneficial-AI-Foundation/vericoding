// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
spec fn contains_all(tr_list: Seq<i32>, ts_list: Seq<i32>) -> bool {
    forall|t: i32| ts_list.contains(t) ==> tr_list.contains(t)
}

fn can_ram_win(tr_list: Vec<i32>, dr_list: Vec<i32>, ts_list: Vec<i32>, ds_list: Vec<i32>) -> (result: String)
    ensures
        (result@ == "yes"@) || (result@ == "no"@),
        (result@ == "yes"@) <==> (
            contains_all(tr_list@, ts_list@) && 
            contains_all(dr_list@, ds_list@)
        )
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume(false);
    unreached()
    // impl-end
}
// </vc-code>


}
fn main() {
    // let result1 = can_ram_win(vec![1, 2], vec![1, 3, 2], vec![2], vec![3, 2]);
    // println!("{}", result1);
    
    // let result2 = can_ram_win(vec![1, 2], vec![1, 3, 2], vec![2], vec![3, 2, 4]);
    // println!("{}", result2);
    
    // let result3 = can_ram_win(vec![3, 2, 5], vec![2, 100], vec![2], vec![100]);
    // println!("{}", result3);
}