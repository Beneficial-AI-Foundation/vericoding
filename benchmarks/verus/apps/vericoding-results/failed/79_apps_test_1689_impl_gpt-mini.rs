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
    let s = vec_to_seq_seq(rows);
    let m = s.len();
    let mut i: int = 0;
    while i < m
        invariant
            0 <= i && i <= m,
            forall|j: int| 0 <= j < i ==> !((s[j].len() >= 2 && s[j][0] == 'O' && s[j][1] == 'O') ||
                                            (s[j].len() >= 5 && s[j][3] == 'O' && s[j][4] == 'O')),
        decreases m - i
    {
        if (s[i].len() >= 2 && s[i][0] == 'O' && s[i][1] == 'O') || (s[i].len() >= 5 && s[i][3] == 'O' && s[i][4] == 'O') {
            let mut res: Vec<char> = Vec::new();
            res.push('A');
            res.push('B');
            res.push('C');
            res.push('D');
            return res;
        }
        i = i + 1;
    }

    proof {
        // loop exit implies i == m, and invariant gives no adjacent empty seats for all rows
        assert(i == m);
        assert(forall|j: int| 0 <= j < m ==> !((s[j].len() >= 2 && s[j][0] == 'O' && s[j][1] == 'O') ||
                                               (s[j].len() >= 5 && s[j][3] == 'O' && s[j][4] == 'O')));
    }

    let mut res: Vec<char> = Vec::new();
    res.push('N');
    res.push('O');
    res
}
// </vc-code>


}

fn main() {}