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
proof fn input_len_is_two(s: Seq<char>)
    requires
        valid_input(s),
    ensures
        s.len() == 2,
{
    reveal(valid_input);
}

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
    proof {
        reveal(valid_input);
    }
    assert(position@.len() == 2);
    assert(position.len() == position@.len());
    assert(0 < position.len());
    assert(1 < position.len());

    let c0 = position[0];
    let c1 = position[1];

    let file_edge = c0 == 'a' || c0 == 'h';
    let rank_edge = c1 == '1' || c1 == '8';

    let moves: i8 = if file_edge && rank_edge {
        3i8
    } else if file_edge || rank_edge {
        5i8
    } else {
        8i8
    };

    proof {
        reveal(is_corner);
        reveal(is_edge);
        reveal(is_interior);
        reveal(valid_moves);

        assert(position@[0] == c0);
        assert(position@[1] == c1);

        if file_edge && rank_edge {
            assert(is_corner(position@));
            assert(valid_moves(position@) == 3);
        } else if file_edge || rank_edge {
            assert(!(file_edge && rank_edge));
            assert(!is_corner(position@));
            assert(is_edge(position@));
            assert(valid_moves(position@) == 5);
        } else {
            assert(!(file_edge || rank_edge));
            assert(!is_corner(position@));
            assert(!is_edge(position@));
            assert(is_interior(position@));
            assert(valid_moves(position@) == 8);
        }
    }

    moves
}
// </vc-code>


}

fn main() {}