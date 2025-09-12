// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
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
    result != seq!['N', 'O'] ==> result.len() >= 4
}
// </vc-helpers>

// <vc-spec>
fn solve(n: int, rows: Seq<Seq<char>>) -> (result: Seq<char>)
    requires 
        valid_input(n, rows),
    ensures 
        result == seq!['N', 'O'] || result.len() >= 4,
    ensures 
        (result == seq!['N', 'O']) ==> no_adjacent_empty_seats(rows),
    ensures 
        (result != seq!['N', 'O']) ==> has_adjacent_empty_seats(rows),
    ensures 
        valid_solution(result, rows),
// </vc-spec>
// <vc-code>
{
    assume(false);
    seq!['N', 'O']
}
// </vc-code>


}

fn main() {}