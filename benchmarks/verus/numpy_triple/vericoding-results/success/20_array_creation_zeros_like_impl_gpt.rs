// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): lemma that adding zero to i32 leaves it unchanged */
proof fn lemma_add_zero_i32(x: i32)
    ensures
        x + 0 == x,
        0 + x == x
{ }
// </vc-helpers>

// <vc-spec>
fn zeros_like(a: &Vec<i32>) -> (result: Vec<i32>)
    ensures 
        result.len() == a.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i] == 0,
        forall|v: &Vec<i32>| v.len() == result.len() ==> {
            forall|i: int| 0 <= i < result.len() ==> 
                result[i] + v[i] == v[i] && v[i] + result[i] == v[i]
        }
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): build zero vector matching a.len() and prove additive identity with forall */
    let n: usize = a.len() as usize;
    let mut r: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            0 <= i as int <= n as int,
            r.len() == i as int,
            forall|k: int| 0 <= k < r.len() ==> r[k] == 0
        decreases (n as int) - (i as int)
    {
        r.push(0);
        i = i + 1;
    }
    proof {
        assert(r.len() == n as int);
        assert forall |v: &Vec<i32>| v.len() == r.len() ==>
            forall |j: int| 0 <= j < r.len() ==> r[j] + v[j] == v[j] && v[j] + r[j] == v[j]
        by {
            assert forall |j: int| 0 <= j < r.len() ==> r[j] + v[j] == v[j] && v[j] + r[j] == v[j]
            by {
                if 0 <= j < r.len() {
                    assert(r[j] == 0);
                    // r[j] + v[j] == v[j]
                    assert(r[j] + v[j] == 0 + v[j]);
                    lemma_add_zero_i32(v[j]);
                    assert(0 + v[j] == v[j]);
                    assert(r[j] + v[j] == v[j]);
                    // v[j] + r[j] == v[j]
                    assert(v[j] + r[j] == v[j] + 0);
                    assert(v[j] + 0 == v[j]);
                    assert(v[j] + r[j] == v[j]);
                }
            };
        };
        assert(n as int == a.len());
    }
    r
}
// </vc-code>

}
fn main() {}