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
    v@.map(|i: int, row: Vec<char>| row@)
}

spec fn row_has_adjacent_0_1(row: Seq<char>) -> bool {
    row.len() >= 2 && row[0] == 'O' && row[1] == 'O'
}

spec fn row_has_adjacent_3_4(row: Seq<char>) -> bool {
    row.len() >= 5 && row[3] == 'O' && row[4] == 'O'
}

spec fn has_adjacent_in_row(row: Seq<char>) -> bool {
    row_has_adjacent_0_1(row) || row_has_adjacent_3_4(row)
}

proof fn lemma_no_adjacent_implies_both_false(row: Seq<char>)
    requires
        row.len() >= 5,
        !has_adjacent_in_row(row)
    ensures
        !row_has_adjacent_0_1(row),
        !row_has_adjacent_3_4(row)
{
}

/* helper modified by LLM (iteration 5): fix compilation error by removing spec mode function */
fn has_adjacent_empty_seats_exec(rows: Vec<Vec<char>>) -> (res: bool)
    ensures
        res == has_adjacent_empty_seats(vec_to_seq_seq(rows))
{
    let mut i = 0;
    let n = rows.len();
    while i < n
        invariant
            0 <= i <= n,
            forall|j: int| 0 <= j < i ==> !has_adjacent_in_row(rows@[j]@),
            res == exists|j: int| 0 <= j < i && has_adjacent_in_row(rows@[j]@)
    {
        let row = &rows[i];
        if row_has_adjacent_0_1(row@) || row_has_adjacent_3_4(row@) {
            return true;
        }
        i += 1;
    }
    false
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
{
    /* code modified by LLM (iteration 5): fix compilation error by using exec mode function */
    let has_adjacent = has_adjacent_empty_seats_exec(rows.clone());
    
    if has_adjacent {
        let mut result_vec = Vec::new();
        result_vec.push('Y');
        result_vec.push('E');
        result_vec.push('S');
        result_vec
    } else {
        vec!['N', 'O']
    }
}
// </vc-code>


}

fn main() {}