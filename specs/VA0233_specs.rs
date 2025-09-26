// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(position: Seq<char>) -> bool {
  position.len() == 2 && 
  'a' <= position[0] && position[0] <= 'h' && 
  '1' <= position[1] && position[1] <= '8'
}

spec fn is_corner(position: Seq<char>) -> bool
  recommends valid_input(position)
{
  (position[0] == 'a' || position[0] == 'h') && 
  (position[1] == '1' || position[1] == '8')
}

spec fn is_edge(position: Seq<char>) -> bool
  recommends valid_input(position)
{
  (position[0] == 'a' || position[0] == 'h' || 
   position[1] == '1' || position[1] == '8') && 
  !is_corner(position)
}

spec fn is_interior(position: Seq<char>) -> bool
  recommends valid_input(position)
{
  !is_corner(position) && !is_edge(position)
}

spec fn valid_moves(position: Seq<char>) -> int
  recommends valid_input(position)
{
  if is_corner(position) { 3 }
  else if is_edge(position) { 5 }
  else { 8 }
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn solve(position: Vec<char>) -> (moves: i8)
  requires 
    valid_input(position@),
  ensures 
    moves as int == valid_moves(position@),
    is_corner(position@) ==> moves == 3,
    is_edge(position@) ==> moves == 5,
    is_interior(position@) ==> moves == 8,
    moves == 3 || moves == 5 || moves == 8,
// </vc-spec>
// <vc-code>
{
  assume(false);
  unreached()
}
// </vc-code>


}

fn main() {}