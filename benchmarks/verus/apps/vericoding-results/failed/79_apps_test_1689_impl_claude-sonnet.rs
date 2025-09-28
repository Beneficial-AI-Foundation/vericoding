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
/* helper modified by LLM (iteration 5): Added decreases clause to i8_to_char_vec function */
spec fn vec_to_seq_seq(v: Vec<Vec<char>>) -> Seq<Seq<char>> {
    v@.map(|i, row: Vec<char>| row@)
}

spec fn row_has_adjacent_empty_at_left(row: Vec<char>) -> bool {
    row.len() >= 2 && row@[0] == 'O' && row@[1] == 'O'
}

spec fn row_has_adjacent_empty_at_right(row: Vec<char>) -> bool {
    row.len() >= 5 && row@[3] == 'O' && row@[4] == 'O'
}

spec fn row_has_adjacent_empty(row: Vec<char>) -> bool {
    row_has_adjacent_empty_at_left(row) || row_has_adjacent_empty_at_right(row)
}

proof fn lemma_has_adjacent_equiv(rows: Vec<Vec<char>>)
    ensures
        has_adjacent_empty_seats(vec_to_seq_seq(rows)) == (exists|i: int| 0 <= i < rows.len() && row_has_adjacent_empty(rows@[i]))
{
}

proof fn lemma_no_adjacent_equiv(rows: Vec<Vec<char>>)
    ensures
        no_adjacent_empty_seats(vec_to_seq_seq(rows)) == (forall|i: int| 0 <= i < rows.len() ==> !row_has_adjacent_empty(rows@[i]))
{
}

fn digit_to_char(digit: u8) -> (result: char)
    requires digit < 10
    ensures result == ('0' as u8 + digit) as char
{
    ('0' as u8 + digit) as char
}

fn i8_to_char_vec(n: i8) -> (result: Vec<char>)
    requires n >= 0
    ensures result.len() >= 1
{
    let mut digits = Vec::new();
    let mut num = n;
    
    if num == 0 {
        digits.push('0');
        return digits;
    }
    
    while num > 0
        invariant num >= 0
        decreases num
    {
        let digit = (num % 10) as u8;
        digits.push(digit_to_char(digit));
        num = num / 10;
    }
    
    let mut result = Vec::new();
    let mut i = digits.len();
    while i > 0
        invariant 0 <= i <= digits.len()
        decreases i
    {
        i = i - 1;
        result.push(digits[i]);
    }
    
    result
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
    /* code modified by LLM (iteration 5): Added decreases clause to main while loop */
    let mut i = 0;
    
    while i < n
        invariant
            0 <= i <= n,
            n >= 0,
            valid_input(n as int, vec_to_seq_seq(rows)),
            forall|j: int| 0 <= j < i ==> !row_has_adjacent_empty(rows@[j])
        decreases n - i
    {
        let row = &rows[i as usize];
        
        if row.len() >= 2 && row[0] == 'O' && row[1] == 'O' {
            let mut result = Vec::new();
            result.push(row[0]);
            result.push(row[1]);
            
            let row_idx_chars = i8_to_char_vec(i);
            let mut j = 0;
            while j < row_idx_chars.len()
                invariant 0 <= j <= row_idx_chars.len()
                decreases row_idx_chars.len() - j
            {
                result.push(row_idx_chars[j]);
                j = j + 1;
            }
            
            proof {
                lemma_has_adjacent_equiv(rows);
                assert(row_has_adjacent_empty(rows@[i as int]));
                assert(has_adjacent_empty_seats(vec_to_seq_seq(rows)));
            }
            
            return result;
        }
        
        if row.len() >= 5 && row[3] == 'O' && row[4] == 'O' {
            let mut result = Vec::new();
            result.push(row[3]);
            result.push(row[4]);
            
            let row_idx_chars = i8_to_char_vec(i);
            let mut j = 0;
            while j < row_idx_chars.len()
                invariant 0 <= j <= row_idx_chars.len()
                decreases row_idx_chars.len() - j
            {
                result.push(row_idx_chars[j]);
                j = j + 1;
            }
            
            proof {
                lemma_has_adjacent_equiv(rows);
                assert(row_has_adjacent_empty(rows@[i as int]));
                assert(has_adjacent_empty_seats(vec_to_seq_seq(rows)));
            }
            
            return result;
        }
        
        i = i + 1;
    }
    
    proof {
        lemma_no_adjacent_equiv(rows);
        assert(forall|j: int| 0 <= j < n ==> !row_has_adjacent_empty(rows@[j]));
        assert(no_adjacent_empty_seats(vec_to_seq_seq(rows)));
    }
    
    let mut result = Vec::new();
    result.push('N');
    result.push('O');
    result
}
// </vc-code>


}

fn main() {}