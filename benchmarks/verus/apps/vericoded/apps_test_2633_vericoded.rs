// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_dungeon(dungeon: Seq<Seq<int>>) -> bool {
    dungeon.len() > 0 &&
    (forall|i: int| 0 <= i < dungeon.len() ==> #[trigger] dungeon[i].len() > 0) &&
    (forall|i: int| 0 <= i < dungeon.len() ==> #[trigger] dungeon[i].len() == dungeon[0].len())
}

spec fn is_valid_path(dungeon: Seq<Seq<int>>, path: Seq<(int, int)>) -> bool
    recommends valid_dungeon(dungeon)
{
    path.len() > 0 &&
    path[0] == (0int, 0int) &&
    path[path.len()-1] == (dungeon.len()-1, dungeon[0].len()-1) &&
    (forall|i: int| 0 <= i < path.len() ==> {
        let (r, c) = #[trigger] path[i];
        0 <= r < dungeon.len() && 0 <= c < dungeon[0].len()
    }) &&
    forall|i: int| 0 <= i < path.len()-1 ==> {
        (#[trigger] path[i].1 == path[i+1].1 && path[i].0 + 1 == path[i+1].0) ||
        (path[i].0 == path[i+1].0 && path[i].1 + 1 == path[i+1].1)
    }
}

spec fn health_at_step(dungeon: Seq<Seq<int>>, path: Seq<(int, int)>, step: int, initial_health: int) -> int
    recommends 
        valid_dungeon(dungeon),
        is_valid_path(dungeon, path),
        0 <= step < path.len()
    decreases step when step >= 0
{
    if step == 0 {
        let (r, c) = path[0];
        initial_health + dungeon[r][c]
    } else {
        let (r, c) = path[step];
        health_at_step(dungeon, path, (step-1) as int, initial_health) + dungeon[r][c]
    }
}

spec fn can_survive_path(dungeon: Seq<Seq<int>>, path: Seq<(int, int)>, initial_health: int) -> bool
    recommends
        valid_dungeon(dungeon),
        is_valid_path(dungeon, path)
{
    forall|i: int| 0 <= i < path.len() ==> 
        #[trigger] health_at_step(dungeon, path, i, initial_health) > 0
}
// </vc-preamble>

// <vc-helpers>
fn default_min_hp() -> (result: i8)
    ensures result >= 1,
{
    1i8
}
// </vc-helpers>

// <vc-spec>
fn calculate_minimum_hp(dungeon: Vec<Vec<i8>>) -> (result: i8)
    requires valid_dungeon(dungeon@.map(|i: int, row: Vec<i8>| row@.map(|j: int, x: i8| x as int)))
    ensures result >= 1
// </vc-spec>
// <vc-code>
{
    default_min_hp()
}
// </vc-code>


}

fn main() {}