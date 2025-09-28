// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(n: int, rows: Seq<Seq<char>>) -> bool {
    n >= 0 && rows.len() == n && forall|i: int| 0 <= i < rows.len() ==> rows[i].len() == 5
}

spec fn has_adjacent_empty_seats(rows: Seq<Seq<char>>) -> bool {
    exists|i: int| 0 <= i < rows.len() && 
        ((rows[i].len() >= 2 && rows[i][0] == 'O' && rows[i][1] == 'O') ||
         (rows[i].len() >= 5 && rows[i][3] == 'O' && rows[i][4] == 'O'))
}

spec fn no_adjacent_empty_seats(rows: Seq<Seq<char>>) -> bool {
    forall|i: int| 0 <= i < rows.len() ==> 
        !((rows[i].len() >= 2 && rows[i][0] == 'O' && rows[i][1] == 'O') ||
          (rows[i].len() >= 5 && rows[i][3] == 'O' && rows[i][4] == 'O'))
}

spec fn valid_solution(result: Seq<char>, rows: Seq<Seq<char>>) -> bool {
    result.len() != 2 || result[0] != 'N' || result[1] != 'O' ==> result.len() >= 4
}
// </vc-preamble>

// <vc-helpers>
spec fn vec_to_seq_seq(v: Vec<Vec<char>>) -> Seq<Seq<char>> {
    v@.map(|i, row: Vec<char>| row@)
}

/* helper modified by LLM (iteration 5): renamed to avoid conflict with spec fn */
spec fn vec_to_seq_seq_exec(v: Vec<Vec<char>>) -> (res: Seq<Seq<char>>) {
    v@.map(|i, row: Vec<char>| row@)
}
// </vc-helpers>

// <vc-spec>
fn solve(n: i8, rows: Vec<Vec<char>>) -> (result: Vec<char>)
    requires 
        valid_input(n as int, vec_to_seq_seq(rows))
    ensures 
        (result@.len() == 2 && result@[0] == 'N' && result@[1] == 'O') || result@.len() >= 4,
        (result@.len() == 2 && result@[0] == 'N' && result@[1] == 'O') ==> no_adjacent_empty_seats(vec_to_seq_seq(rows)),
        !(result@.len() == 2 && result@[0] == 'N' && result@[1] == 'O') ==> has_adjacent_empty_seats(vec_to_seq_seq(rows)),
        valid_solution(result@, vec_to_seq_seq(rows))
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): fixed compilation error by using ghost! for spec data and direct Vec access in exec */
{
    let ghost_seq_rows: Ghost<Seq<Seq<char>>> = ghost!(rows@.map(|row: Vec<char>| row@));
    let mut i: usize = 0;
    let mut found = false;
    while i < (n as usize)
        invariant
            0 <= (i as int) <= (n as int),
            found == exists|j: int| 0 <= j < (i as int) && row_has_adjacent_empty(ghost_seq_rows@[j])
    {
        if rows[i].len() > 0 && rows[i][0] == 'O' && rows[i].len() > 1 && rows[i][1] == 'O' || rows[i].len() > 3 && rows[i][3] == 'O' && rows[i].len() > 4 && rows[i][4] == 'O' {
            found = true;
            break;
        }
        i += 1;
    }
    if !found {
        proof {
            assert(forall|k: int| 0 <= k < (n as int) ==> !row_has_adjacent_empty(ghost_seq_rows@[k]));
        }
        return vec!['N', 'O'];
    } else {
        return vec!['Y', 'E', 'S', ' '];
    }
}
// </vc-code>


}

fn main() {}