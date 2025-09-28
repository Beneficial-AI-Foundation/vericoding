// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn is_subseq_at(sub: Vec<i32>, main: Vec<i32>, i: int) -> bool {
    0 <= i && i + sub.len() <= main.len() && 
    (forall|j: int| 0 <= j < sub.len() ==> sub[j] == main[i + j])
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn is_sublist(sub: &Vec<i32>, main: &Vec<i32>) -> (result: bool)
    ensures
        result <==> exists|i: int| is_subseq_at(*sub, *main, i),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 4): Fix type mismatch by casting i to int in assert */
    if sub.len() > main.len() {
        return false;
    }
    let delta = main.len() - sub.len();
    for i in 0..(delta + 1) {
        let mut match_ = true;
        for j in 0..sub.len() {
            if sub[j] != main[i + j] {
                match_ = false;
                break;
            }
        }
        if match_ {
            proof {
                assert(is_subseq_at((*sub), (*main), i as int));
            }
            return true;
        }
    }
    false
}
// </vc-code>

}
fn main() {}