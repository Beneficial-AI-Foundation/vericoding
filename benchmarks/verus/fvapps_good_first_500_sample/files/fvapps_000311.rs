// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
#[derive(PartialEq, Eq)]
pub enum GameResult {
    Alice,
    Bob,
    Tie,
}

fn stone_game_iii(stones: Vec<i32>) -> (result: GameResult)
    requires stones.len() >= 1,
    ensures 
        result == GameResult::Alice || result == GameResult::Bob || result == GameResult::Tie
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume(false);
    GameResult::Tie
    // impl-end
}
// </vc-code>


}
fn main() {
    // let test1 = vec![1, 2, 3, 7];
    // println!("{:?}", stone_game_iii(test1));
    // 
    // let test2 = vec![1, 2, 3, -9]; 
    // println!("{:?}", stone_game_iii(test2));
    //
    // let test3 = vec![1, 2, 3, 6];
    // println!("{:?}", stone_game_iii(test3));
}