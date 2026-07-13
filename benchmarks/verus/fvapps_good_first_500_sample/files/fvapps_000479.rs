// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
spec fn is_valid_path(rooms: Seq<Vec<nat>>, path: Seq<nat>) -> bool {
    path.len() > 0 &&
    path[0] == 0 &&
    (forall|j: int| 0 <= j < path.len() - 1 ==> {
        j + 1 < path.len() &&
        path[j] < rooms.len() &&
        path[j + 1] < rooms.len() &&
        rooms[path[j] as int]@.contains(path[j + 1])
    })
}

spec fn can_reach_room(rooms: Seq<Vec<nat>>, target_room: nat) -> bool {
    target_room < rooms.len() &&
    exists|path: Seq<nat>| {
        is_valid_path(rooms, path) &&
        path[path.len() - 1] == target_room
    }
}

fn can_visit_all_rooms(rooms: Vec<Vec<nat>>) -> (result: bool)
    requires 
        rooms.len() >= 1,
        rooms.len() <= 1000,
        forall|i: int| 0 <= i < rooms.len() ==> rooms[i].len() <= 1000,
        forall|i: int, j: int| 0 <= i < rooms.len() && 0 <= j < rooms[i].len() ==> rooms[i][j] < rooms.len(),
    ensures 
        result == true <==> (forall|i: nat| i < rooms.len() ==> can_reach_room(rooms@, i)),
        result == false <==> (exists|i: nat| i < rooms.len() && !can_reach_room(rooms@, i))
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
    // let test1 = vec![vec![1], vec![2], vec![3], vec![]];
    // println!("{}", can_visit_all_rooms(test1));
    
    // let test2 = vec![vec![1, 3], vec![3, 0, 1], vec![2], vec![0]];
    // println!("{}", can_visit_all_rooms(test2));
    
    // let test3 = vec![vec![1], vec![2], vec![3], vec![], vec![], vec![]];
    // println!("{}", can_visit_all_rooms(test3));
}