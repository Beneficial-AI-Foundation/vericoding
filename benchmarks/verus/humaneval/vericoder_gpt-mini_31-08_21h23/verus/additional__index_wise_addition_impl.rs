use vstd::prelude::*;

verus! {

// <vc-helpers>
fn build_row(a_row: &Vec<i32>, b_row: &Vec<i32>, j: int) -> Vec<i32>
    requires 0 <= j && j <= a_row.len();
    requires a_row.len() == b_row.len();
    requires forall|k: int| 0 <= k < a_row.len() ==> a_row[k] + b_row[k] <= i32::MAX;
    requires forall|k: int| 0 <= k < a_row.len() ==> a_row[k] + b_row[k] >= i32::MIN;
    ensures result.len() == a_row.len() - j;
    ensures forall |l: int| 0 <= l < result.len() ==> result[l] == a_row[j + l] + b_row[j + l];
    decreases a_row.len() - j;
{
    if j == a_row.len() {
        Vec::new()
    } else {
        let sum: i32 = a_row[j] + b_row[j];
        let tail = build_row(a_row, b_row, j + 1);
        let mut v: Vec<i32> = Vec::new();
        v.push(sum);
        v.append(tail);
        // proofs about v follow from properties of tail and the push/append operations
        proof {
            assert(v.len() == a_row.len() - j);
            // element 0
            assert(v[0] == sum);
            // elements >=1 come from tail
            assert(forall |l: int| 1 <= l < v.len() ==> v[l] == a_row[j + l] + b_row[j + l]);
        }
        v
    }
}

fn build_suffix(a: &Vec<Vec<i32>>, b: &Vec<Vec<i32>>, i: int) -> Vec<Vec<i32>>
    requires 0 <= i && i <= a.len();
    requires a.len() == b.len();
    requires forall|p: int| 0 <= p < a.len() ==> a[p].len() == b[p].len();
    requires forall|p: int| 0 <= p < a.len() ==>
        forall|q: int| 0 <= q < a[p].len() ==> a[p][q] + b[p][q] <= i32::MAX;
    requires forall|p: int| 0 <= p < a.len() ==>
        forall|q: int| 0 <= q < a[p].len() ==> a[p][q] + b[p][q] >= i32::MIN;
    ensures result.len() == a.len() - i;
    ensures forall |l: int| 0 <= l < result.len() ==>
        result[l].len() == a[i + l].len();
    ensures forall |l: int| 0 <= l < result.len() ==>
        forall |m: int| 0 <= m < result[l].len() ==> result[l][m] == a[i + l][m] + b[i + l][m];
    decreases a.len() - i;
{
    if i == a.len() {
        Vec::new()
    } else {
        let row = build_row(&a[i], &b[i], 0);
        let tail = build_suffix(a, b, i + 1);
        let mut v: Vec<Vec<i32>> = Vec::new();
        v.push(row);
        v.append(tail);
        proof {
            assert(v.len() == a.len() - i);
            assert(v[0].len() == a[i].len());
            assert(forall |m: int| 0 <= m < v[0].len() ==> v[0][m] == a[i][m] + b[i][m]);
            assert(forall |l: int| 1 <= l < v.len() ==> v[l].len() == a[i + l].len());
            assert(forall |l: int| 1 <= l < v.len() ==>
                forall |m: int| 0 <= m < v[l].len() ==> v[l][m] == a[i + l][m] + b[i + l][m]);
        }
        v
    }
}
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
    build_suffix(a, b, 0)
}
// </vc-code>

fn main() {}
}