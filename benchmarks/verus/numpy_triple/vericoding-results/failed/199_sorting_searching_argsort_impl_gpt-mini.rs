// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): convert usize to int as a spec function */
spec fn usize_to_int(u: usize) -> int { u as int }
// </vc-helpers>

// <vc-spec>
fn argsort(a: Vec<i8>) -> (result: Vec<usize>)
    ensures 
        result.len() == a.len(),

        forall|i: int| 0 <= i < result.len() ==> #[trigger] result[i] < a.len(),

        forall|i: int, j: int| 0 <= i < j < result.len() ==> 
            a[#[trigger] result[i] as int] <= a[#[trigger] result[j] as int],

        forall|i: int, j: int| 0 <= i < j < result.len() && 
            a[#[trigger] result[i] as int] == a[#[trigger] result[j] as int] ==> 
            result[i] < result[j]
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): implement argsort by scanning all i8 values and pushing matching indices */
    let n = a.len();
    let mut result: Vec<usize> = Vec::new();

    let mut val: i8 = i8::MIN;
    loop {
        let mut i: usize = 0;
        while i < n {
            if a[i] == val {
                result.push(i);
            }
            i += 1;
        }
        if val == i8::MAX {
            break;
        }
        val = (val as i16 + 1) as i8;
    }

    proof {
        // Every original index appears in result because the outer loop iterated all possible i8 values
        forall|idx: int| 0 <= idx < n as int ==> {
            let ui: usize = idx as usize;
            assert(exists|k: int| 0 <= k < result.len() && result[k as usize] == ui);
        };

        assert(result.len() == n);

        forall|p: int, q: int| 0 <= p < q < result.len() ==> {
            let rp: usize = result[p as usize];
            let rq: usize = result[q as usize];
            assert(a[rp] <= a[rq]);
        };

        forall|p: int, q: int| 0 <= p < q < result.len() && a[result[p as usize]] == a[result[q as usize]] ==> {
            let rp: usize = result[p as usize];
            let rq: usize = result[q as usize];
            assert(rp < rq);
        };
    }

    result
}
// </vc-code>

}
fn main() {}