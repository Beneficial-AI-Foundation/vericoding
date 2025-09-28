// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): remove unused helpers and convert to proper ghost code */
proof fn nat_to_int_lemma(n: nat)
    ensures
        n as int >= 0
{
}

proof fn nat_arithmetic_lemma(n: nat, m: nat)
    ensures
        (n + m) as int == n as int + m as int
{
}
// </vc-helpers>

// <vc-spec>
fn polycompanion(c: Vec<i8>) -> (result: Vec<Vec<i8>>)
    requires 
        c.len() >= 2,
        c[c.len() - 1] != 0,
    ensures
        result.len() == c.len() - 1,
        forall|i: int| 0 <= i < result.len() ==> result[i].len() == c.len() - 1,
        forall|i: int, j: int| 
            0 <= i < result.len() && 0 <= j < result[i].len() ==>
            (if i + 1 == j && i < c.len() - 2 {
                result[i][j] as int == 1
            } else if i == c.len() - 2 {
                result[i][j] as int * c[c.len() - 1] as int == -c[j] as int
            } else {
                result[i][j] as int == 0
            })
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fix nat/int conversion in loop invariants */
    let n: usize = c.len();
    let mut result: Vec<Vec<i8>> = Vec::new();
    let mut i: usize = 0;
    while i < n - 1
        invariant
            i <= n - 1,
            result.len() == i,
            forall|k: int| 0 <= k < i as int ==> result[k as usize].len() == n - 1,
            forall|k: int, l: int| 0 <= k < i as int && 0 <= l < (n - 1) as int ==> (if k + 1 == l && k < (n - 2) as int {
                result[k as usize][l as usize] as int == 1
            } else if k == (n - 2) as int {
                result[k as usize][l as usize] as int * c[n - 1] as int == -c[l as usize] as int
            } else {
                result[k as usize][l as usize] as int == 0
            })
    {
        let mut row: Vec<i8> = Vec::with_capacity(n - 1);
        let mut j: usize = 0;
        while j < n - 1
            invariant
                j <= n - 1,
                row.len() == j,
                forall|l: int| 0 <= l < j as int ==> (if i as int + 1 == l && i < n - 2 {
                    row[l as usize] as int == 1
                } else if i == n - 2 {
                    row[l as usize] as int * c[n - 1] as int == -c[l as usize] as int
                } else {
                    row[l as usize] as int == 0
                })
        {
            if i as int + 1 == j as int && i < n - 2 {
                row.push(1);
            } else if i == n - 2 {
                proof {
                    assert(c[n - 1] != 0);
                }
                row.push(-c[j]);
            } else {
                row.push(0);
            }
            j = j + 1;
        }
        result.push(row);
        i = i + 1;
    }
    result
}
// </vc-code>


}
fn main() {}