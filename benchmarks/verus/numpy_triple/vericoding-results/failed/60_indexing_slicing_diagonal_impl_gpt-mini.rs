// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): compute diagonal length in specification */
spec fn diag_len(rows: nat, cols: nat, offset: i32) -> nat
    requires
        if offset >= 0 { offset as int <= cols as int } else { (-offset) as int <= rows as int },
    ensures
        result ==
            if offset >= 0 {
                if rows as int <= cols as int - offset as int { rows } else { (cols as int - offset as int) as nat }
            } else {
                if rows as int + (-offset) as int <= cols as int { (rows as int + (-offset) as int) as nat } else { cols }
            },
{
    if offset >= 0 {
        let off = offset as int;
        if rows as int <= cols as int - off {
            rows
        } else {
            (cols as int - off) as nat
        }
    } else {
        let off = (-offset) as int;
        if rows as int + off <= cols as int {
            (rows as int + off) as nat
        } else {
            cols
        }
    }
}
// </vc-helpers>

// <vc-spec>
fn diagonal(a: Vec<Vec<f64>>, offset: i32) -> (result: Vec<f64>)
    requires 
        a@.len() > 0,
        a@.len() > 0 ==> a@[0].len() > 0,
        forall|i: int| 0 <= i < a@.len() ==> #[trigger] a@[i].len() == a@[0].len(),
        if offset >= 0 { 
            offset as int <= a@[0].len() as int
        } else { 
            (-offset) as int <= a@.len() as int
        },
    ensures
        result@.len() == (if offset >= 0 { 
            if a@.len() as int <= (a@[0].len() as int - offset as int) { a@.len() as int } else { a@[0].len() as int - offset as int }
        } else { 
            if (a@.len() as int + (-offset) as int) <= a@[0].len() as int { a@.len() as int + (-offset) as int } else { a@[0].len() as int }
        }) as usize,
        forall|i: int| 0 <= i < result@.len() ==> {
            if offset >= 0 {
                #[trigger] result@[i] == a@[i][i + offset as int]
            } else {
                #[trigger] result@[i] == a@[i + (-offset) as int][i]
            }
        },
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): compute diagonal and maintain invariants */
{
    let rows: usize = a.len();
    let cols: usize = a[0].len();
    let n: usize = if offset >= 0 {
        let off = offset as usize;
        if rows <= cols - off { rows } else { cols - off }
    } else {
        let off = (-offset) as usize;
        if rows + off <= cols { rows + off } else { cols }
    };
    let mut result: Vec<f64> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            result@.len() == i as nat,
            forall|j: int| 0 <= j < i as int ==>
                if offset >= 0 {
                    result@[j] == a@[j][j + offset as int]
                } else {
                    result@[j] == a@[j + (-offset) as int][j]
                },
        decreases n - i
    {
        if offset >= 0 {
            let off = offset as usize;
            let row = i;
            let col = i + off;
            proof {
                assert(row as int < a@.len() as int);
                assert(col as int < a@[row as int].len() as int);
                assert(a@[row as int].len() == a@[0].len());
            }
            result.push(a[row][col]);
        } else {
            let off = (-offset) as usize;
            let row = i + off;
            let col = i;
            proof {
                assert(row as int < a@.len() as int);
                assert(col as int < a@[row as int].len() as int);
                assert(a@[row as int].len() == a@[0].len());
            }
            result.push(a[row][col]);
        }
        i += 1;
    }
    result
}
// </vc-code>

}
fn main() {}