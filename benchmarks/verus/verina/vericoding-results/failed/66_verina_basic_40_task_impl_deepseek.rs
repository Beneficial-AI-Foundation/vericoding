// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn second_smallest_precond(s: &Vec<i32>) -> bool {
    s.len() > 1
}

spec fn second_smallest_postcond(s: &Vec<i32>, result: i32) -> bool {
    (exists|i: int| 0 <= i < s.len() && s[i] == result) &&
    (exists|j: int| 0 <= j < s.len() && s[j] < result &&
        (forall|k: int| 0 <= k < s.len() && s[k] != s[j] ==> s[k] >= result))
}
// </vc-preamble>

// <vc-helpers>
proof fn lemma_exists_min(s: Seq<int>) 
    requires 
        s.len() >= 1
    ensures 
        exists|min_val: int| (#[trigger] s.contains(min_val)) && (forall|k: int| 0 <= k < s.len() ==> min_val <= s[k])
{
    if s.len() == 1 {
        assert(s.contains(s[0]));
        assert(forall|k: int| 0 <= k < s.len() ==> s[0] <= s[k]);
    } else {
        let subseq = s.subrange(0, s.len() - 1 as int);
        lemma_exists_min(subseq);
        assert(exists|min_sub: int| #[trigger] subseq.contains(min_sub) && (forall|k: int| 0 <= k < subseq.len() ==> min_sub <= subseq[k]));
        assert(s.contains(s[s.len() - 1]));
        assert(forall|k: int| 0 <= k < s.len()| {
            if k == s.len() - 1 { s[s.len() - 1] <= s[s.len() - 1] } 
            else { min_sub <= subseq[k] && subseq[k] == s[k] }
        });
    }
}
// </vc-helpers>

// <vc-spec>
fn second_smallest(s: &Vec<i32>) -> (result: i32) 
    requires second_smallest_precond(s) 
    ensures second_smallest_postcond(s, result)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed compilation error with exists syntax and improved verification */
    let s_seq = s.view();
    proof { lemma_exists_min(s_seq); }
    
    let mut min_val = s[0];
    let mut second_min = s[1];
    if second_min < min_val {
        let temp = min_val;
        min_val = second_min;
        second_min = temp;
    }
    let mut i = 2;
    while i < s.len()
        invariant 
            i <= s.len(),
            min_val == s_seq[i-1] || min_val == s_seq[i-2],
            second_min == s_seq[i-1] || second_min == s_seq[i-2],
            min_val <= second_min,
            exists|j: int| 0 <= j < i && s_seq[j] == min_val,
            exists|k: int| 0 <= k < i && s_seq[k] == second_min,
            (forall|p: int| 0 <= p < i ==> min_val <= s_seq[p]),
            (forall|q: int| 0 <= q < i && s_seq[q] != min_val ==> second_min <= s_seq[q])
        decreases s.len() - i
    {
        let current = s[i];
        if current < min_val {
            second_min = min_val;
            min_val = current;
        } else if current < second_min && current != min_val {
            second_min = current;
        }
        i = i + 1;
        
        proof {
            assert(forall|q: int| 0 <= q < i && s_seq[q] != min_val ==> second_min <= s_seq[q]);
        }
    }
    second_min
}
// </vc-code>

}
fn main() {}