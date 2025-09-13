// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn valid_dungeon(dungeon: Seq<Seq<int>>) -> bool {
    dungeon.len() > 0 &&
    (forall|i: int| 0 <= i < dungeon.len() ==> dungeon[i].len() > 0) &&
    (forall|i: int| 0 <= i < dungeon.len() ==> dungeon[i].len() == dungeon[0].len())
}

spec fn is_valid_path(dungeon: Seq<Seq<int>>, path: Seq<(int, int)>) -> bool {
    valid_dungeon(dungeon) ==>
    path.len() > 0 &&
    path[0] == (0int, 0int) &&
    path[path.len()-1] == (dungeon.len()-1, dungeon[0].len()-1) &&
    (forall|i: int| 0 <= i < path.len() ==> {
        let (r, c) = path[i];
        0 <= r < dungeon.len() && 0 <= c < dungeon[0].len()
    }) &&
    forall|i: int| 0 <= i < path.len()-1 ==> 
        (path[i].1 == path[i+1].1 && path[i].0 + 1 == path[i+1].0) ||
        (path[i].0 == path[i+1].0 && path[i].1 + 1 == path[i+1].1)
}

spec fn health_at_step(dungeon: Seq<Seq<int>>, path: Seq<(int, int)>, step: int, initial_health: int) -> int
    decreases step
{
    if valid_dungeon(dungeon) && is_valid_path(dungeon, path) && 0 <= step < path.len() {
        if step == 0 {
            let (r, c) = path[0];
            initial_health + dungeon[r][c]
        } else {
            let (r, c) = path[step];
            health_at_step(dungeon, path, step-1, initial_health) + dungeon[r][c]
        }
    } else {
        0
    }
}

spec fn can_survive_path(dungeon: Seq<Seq<int>>, path: Seq<(int, int)>, initial_health: int) -> bool {
    valid_dungeon(dungeon) && is_valid_path(dungeon, path) ==>
    forall|i: int| 0 <= i < path.len() ==> 
        health_at_step(dungeon, path, i, initial_health) > 0
}
// </vc-helpers>

// <vc-spec>
fn calculate_minimum_hp(dungeon: Seq<Seq<int>>) -> (result: int)
    requires valid_dungeon(dungeon)
    ensures result >= 1
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>


}

fn main() {}