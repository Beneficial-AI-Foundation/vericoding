// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn is_peek(v: &Vec<i32>, i: int) -> bool
    recommends 0 <= i < v.len()
{
    forall|k: int| 0 <= k < i ==> v[i] >= v[k]
}

spec fn peek_sum(v: &Vec<i32>, i: int) -> int
    recommends 0 <= i <= v.len()
    decreases i when 0 <= i <= v.len()
{
    if i == 0 {
        0
    } else {
        if is_peek(v, i - 1) {
            v[i - 1] + peek_sum(v, i - 1)
        } else {
            peek_sum(v, i - 1)
        }
    }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): resubmitted from correct previous iteration */
spec fn seq_max(s: Seq<i32>) -> i32
    requires s.len() > 0
    decreases s.len()
{
    if s.len() == 1 {
        s[0]
    } else {
        let sub_max = seq_max(s.subrange(0, s.len() - 1));
        if s.last() > sub_max { s.last() } else { sub_max }
    }
}

proof fn lemma_seq_max_properties(s: Seq<i32>)
    requires s.len() > 0
    ensures
        (forall|i: int| 0 <= i < s.len() ==> s[i] <= seq_max(s)),
        (exists|i: int| 0 <= i < s.len() && s[i] == seq_max(s)),
    decreases s.len()
{
    if s.len() > 1 {
        let sub = s.subrange(0, s.len() - 1);
        lemma_seq_max_properties(sub);
        let sub_max = seq_max(sub);
        if s.last() <= sub_max {
            let j = choose |j: int| 0 <= j < sub.len() && sub[j] == sub_max;
            assert(s[j] == seq_max(s));
        }
    }
}
// </vc-helpers>

// <vc-spec>
fn m_peek_sum(v: &Vec<i32>) -> (sum: i32)
    requires v.len() > 0
    ensures sum == peek_sum(v, v.len() as int)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 3): fixed compilation errors by using v@[] for indexing in proof blocks */
{
    let mut sum = v[0];
    let mut max_so_far = v[0];
    let mut i: usize = 1;

    proof {
        assert(is_peek(v, 0));
        assert(peek_sum(v, 1) == (if is_peek(v, 0) { v@[0] } else { 0 }) + peek_sum(v, 0));
        assert(peek_sum(v, 1) == v@[0]);

        let prefix1 = v.view().subrange(0, 1);
        lemma_seq_max_properties(prefix1);
        assert(seq_max(prefix1) == v@[0]);
    }

    while i < v.len()
        invariant
            1 <= i <= v.len(),
            sum == peek_sum(v, i as int),
            max_so_far == seq_max(v.view().subrange(0, i as int)),
        decreases v.len() - i
    {
        proof {
            let prefix = v.view().subrange(0, i as int);
            lemma_seq_max_properties(prefix);
            assert(is_peek(v, i as int) <==> (v@[i as int] >= max_so_far));
        }

        if v[i] >= max_so_far {
            sum = sum + v[i];
            max_so_far = v[i];
        }
        
        i = i + 1;
    }
    
    sum
}
// </vc-code>

}
fn main() {}