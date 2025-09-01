use vstd::prelude::*;

verus! {

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
#[verifier::loop_isolation(false)]
fn index_wise_addition(a: &Vec<Vec<i32>>, b: &Vec<Vec<i32>>) -> (c: Vec<Vec<i32>>)
    // pre-conditions-start
    requires
        a.len() == b.len(),
        forall|i: int| #![auto] 0 <= i < a.len() ==> a[i].len() == b[i].len(),
        forall|i: int| #![trigger a[i], b[i]]
            0 <= i < a.len()
                ==> forall|j: int| 0 <= j < a[i].len() ==> a[i][j] + b[i][j] <= i32::MAX,
        forall|i: int| #![trigger a[i], b[i]]
            0 <= i < a.len()
                ==> forall|j: int| 0 <= j < a[i].len() ==> a[i][j] + b[i][j] >= i32::MIN,
    // pre-conditions-end
    // post-conditions-start
    ensures
        c.len() == a.len(),
        forall|i: int| #![auto] 0 <= i < c.len() ==> c[i].len() == a[i].len(),
        forall|i: int| #![trigger a[i], b[i], c[i]]
            0 <= i < c.len()
                ==> forall|j: int| #![auto] 0 <= j < c[i].len() ==> c[i][j] == a[i][j] + b[i][j],
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    let mut c: Vec<Vec<i32>> = Vec::new();
    let mut i: usize = 0;
    
    while i < a.len()
        invariant
            i <= a.len(),
            c.len() == i as int,
            forall|k: int| #![auto] 0 <= k < i as int ==> c[k].len() == a[k].len(),
            forall|k: int| #![trigger a[k], b[k], c[k]]
                0 <= k < i as int ==> forall|j: int| #![auto] 0 <= j < c[k].len() ==> c[k][j] == a[k][j] + b[k][j],
    {
        let mut row: Vec<i32> = Vec::new();
        let mut j: usize = 0;
        
        while j < a[i].len()
            invariant
                i < a.len(),
                j <= a[i].len() as int,
                row.len() == j as int,
                forall|k: int| #![auto] 0 <= k < j as int ==> row[k] == a[i as int][k] + b[i as int][k],
        {
            let sum = a[i][j] + b[i][j];
            row.push(sum);
            j = j + 1;
        }
        
        c.push(row);
        i = i + 1;
    }
    
    c
}
// </vc-code>

fn main() {}
}