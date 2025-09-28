// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(n: int, scores: Seq<int>) -> bool {
    n == scores.len() && n >= 1 && exists|i: int| 0 <= i < scores.len() && scores[i] != 0
}

spec fn unique_non_zero_scores(scores: Seq<int>) -> Set<int> {
    Set::new(|x: int| exists|i: int| 0 <= i < scores.len() && scores[i] != 0 && scores[i] == x)
}

spec fn valid_result(scores: Seq<int>, result: int) -> bool {
    result >= 1 && 
    result == unique_non_zero_scores(scores).len() && 
    result <= scores.len()
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): relate mapping of Vec to Seq index */
proof fn vec_map_index(scores: Vec<i8>, idx: int)
    requires
        0 <= idx && idx < scores.len() as int,
    ensures
        scores@.map(|i, x| x as int)@[idx] == scores[idx as usize] as int,
{
    proof {
        // mapping a sequence and indexing equals casting the underlying vec element
        assert(scores@.map(|i, x| x as int)@[idx] == (scores@@[idx]) as int);
        assert(scores@@[idx] == scores[idx as usize]);
    }
}

/* helper modified by LLM (iteration 4): return set with non-zero added */
spec fn add_nonzero(s: Set<int>, v: int) -> Set<int> {
    if v != 0 { s.insert(v) } else { s }
}

// </vc-helpers>

// <vc-spec>
fn solve(n: i8, scores: Vec<i8>) -> (result: i8)
    requires valid_input(n as int, scores@.map(|i, x| x as int))
    ensures valid_result(scores@.map(|i, x| x as int), result as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 4): compute unique non-zero scores into ghost set and return its size */
    let mut i: usize = 0;
    let mut s: Set<int> = Set::empty();
    while i < scores.len()
        invariant
            0 <= i as int && i as int <= scores.len() as int,
            forall|x: int| s.contains(x) <==> exists|k: int| 0 <= k && k < i as int && scores@.map(|j, y| y as int)@[k] == x && x != 0,
        decreases
            scores.len() as int - i as int
    {
        let v: i8 = scores[i];
        if v != 0 {
            ghost {
                s = s.insert(v as int);
            }
        }
        i += 1;
    }
    proof {
        // at loop exit s captures exactly the set of non-zero values in the whole scores sequence
        assert(i as int == scores.len() as int);
        assert(forall|x: int| s.contains(x) <==> exists|k: int| 0 <= k && k < scores.len() as int && scores@.map(|j, y| y as int)@[k] == x && x != 0);
        assert(s == unique_non_zero_scores(scores@.map(|j, y| y as int)));
    }
    let result: i8 = s.len() as i8;
    result
}

// </vc-code>


}

fn main() {}