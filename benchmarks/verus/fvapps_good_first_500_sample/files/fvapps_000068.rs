// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
spec fn has_mine(mine_map: Seq<char>) -> bool {
    exists|i: int| 0 <= i < mine_map.len() && mine_map[i] == '1'
}

spec fn count_mines(mine_map: Seq<char>) -> nat
    decreases mine_map.len()
{
    if mine_map.len() == 0 {
        0
    } else {
        let count_rest = count_mines(mine_map.skip(1));
        if mine_map[0] == '1' {
            count_rest + 1
        } else {
            count_rest
        }
    }
}

fn min_cost_clear_mines(a: u32, b: u32, mine_map: &str) -> (result: u32)
    ensures
        has_mine(mine_map@) ==> result >= a,
        result <= a * count_mines(mine_map@) as u32
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume(false);
    0
    // impl-end
}
// </vc-code>


}
fn main() {
    // println!("{}", min_cost_clear_mines(1, 1, "01000010"));
    // println!("{}", min_cost_clear_mines(5, 1, "01101110"));
    // println!("{}", min_cost_clear_mines(3, 2, "1011"));
}