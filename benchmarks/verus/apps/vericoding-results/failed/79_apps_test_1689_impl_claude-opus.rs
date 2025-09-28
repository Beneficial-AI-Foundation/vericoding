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
/* helper modified by LLM (iteration 4): Added vec_to_seq_seq helper function */
spec fn vec_to_seq_seq(v: Vec<Vec<char>>) -> Seq<Seq<char>> {
    v@.map(|i: int, row: Vec<char>| row@)
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
    /* code modified by LLM (iteration 4): Added decreases clause to while loop */
    let mut i: usize = 0;
    while i < n as usize
        invariant
            0 <= i <= n as int,
            rows.len() == n as int,
            forall|j: int| 0 <= j < rows.len() ==> rows[j].len() == 5,
            forall|j: int| 0 <= j < i ==> 
                !((rows[j]@.len() >= 2 && rows[j]@[0] == 'O' && rows[j]@[1] == 'O') ||
                  (rows[j]@.len() >= 5 && rows[j]@[3] == 'O' && rows[j]@[4] == 'O'))
        decreases n as int - i as int
    {
        let row = &rows[i];
        
        if row.len() >= 2 && row[0] == 'O' && row[1] == 'O' {
            let mut result = Vec::new();
            result.push('Y');
            result.push('E');
            result.push('S');
            result.push('+');
            let row_num = (i + 1) as u8;
            if row_num >= 10 {
                result.push((('0' as u8) + row_num / 10) as char);
            }
            result.push((('0' as u8) + row_num % 10) as char);
            result.push('A');
            return result;
        }
        
        if row.len() >= 5 && row[3] == 'O' && row[4] == 'O' {
            let mut result = Vec::new();
            result.push('Y');
            result.push('E');
            result.push('S');
            result.push('+');
            let row_num = (i + 1) as u8;
            if row_num >= 10 {
                result.push((('0' as u8) + row_num / 10) as char);
            }
            result.push((('0' as u8) + row_num % 10) as char);
            result.push('D');
            return result;
        }
        
        i = i + 1;
    }
    
    let mut result = Vec::new();
    result.push('N');
    result.push('O');
    result
}
// </vc-code>


}

fn main() {}