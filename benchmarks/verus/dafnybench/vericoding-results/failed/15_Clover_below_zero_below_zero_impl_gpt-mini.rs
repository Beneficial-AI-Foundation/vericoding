use vstd::prelude::*;

verus! {

// <vc-helpers>
// Added a small lemma to relate Vec indexing with usize and sequence indexing with int,
// to help the verifier bridge the two styles of indexing used in the implementation.
fn vec_index_eq(operations: &Vec<i32>, j: usize)
    requires
        j < operations.len(),
    ensures
        operations[j] == operations@[j as int]
{
    proof {
        assert(operations[j] == operations@[j as int]);
    }
}
// </vc-helpers>

// <vc-spec>
fn below_zero(operations: Vec<i32>) -> (result: (Vec<i32>, bool))
    ensures
        result.0.len() == operations.len() + 1,
        result.0[0] == 0,
        forall|i: int| 0 <= i < (result.0.len() - 1) as int ==> result.0[i + 1] == result.0[i] + operations[i],
        result.1 == true ==> exists|i: int| 1 <= i <= operations.len() as int && result.0[i] < 0,
        result.1 == false ==> forall|i: int| 0 <= i < result.0.len() as int ==> result.0[i] >= 0,
// </vc-spec>
// <vc-code>
{
    let n = operations.len();
    let mut res: Vec<i32> = Vec::new();
    res.push(0);
    let mut curr: i32 = 0;
    let mut found: bool = false;
    let mut j: usize = 0;
    while j < n
        invariant j <= n;
        invariant res.len() == j + 1;
        invariant res@[j as int] == curr;
        invariant forall |k: int| 0 <= k && k < (j as int) ==> res@[k + 1] == res@[k] + operations@[k];
        invariant found == (exists |k: int| 1 <= k && k <= (j as int) && res@[k] < 0);
        decreases (n - j);
    {
        let prev = curr;
        let op: i32 = operations[j];
        // relate usize-indexed access with int-indexed access for the verifier
        proof {
            vec_index_eq(&operations, j);
        }
        assert(op == operations@[j as int]);
        curr = prev + op;
        res.push(curr);
        assert(res@[(j as int) + 1] == curr);
        assert(res@[j as int] + operations@[j as int] == curr);
        if curr < 0 {
            found = true;
        }
        j = j + 1;
    }
    (res, found)
}
// </vc-code>

fn main() {}

}