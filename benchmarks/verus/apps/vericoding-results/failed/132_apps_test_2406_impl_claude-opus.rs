// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(n: int, heights: Seq<int>) -> bool {
    n > 0 && heights.len() == n &&
    (forall|i: int| 0 <= i < n ==> #[trigger] heights[i] >= 0) &&
    (forall|i: int| 0 <= i < n-1 ==> #[trigger] heights[i] < heights[i+1])
}

spec fn valid_output(n: int, result: Seq<int>) -> bool {
    result.len() == n &&
    (forall|i: int| 0 <= i < n ==> #[trigger] result[i] >= 0) &&
    (forall|i: int| 0 <= i < n-1 ==> #[trigger] result[i] <= result[i+1]) &&
    (forall|i: int| 0 <= i < n-1 ==> #[trigger] result[i+1] - result[i] <= 1)
}

spec fn is_stable(result: Seq<int>) -> bool {
    forall|i: int| 0 <= i < result.len()-1 ==> !(#[trigger] result[i] + 2 <= result[i+1])
}

spec fn sum_seq(s: Seq<int>) -> int
    decreases s.len()
{
    if s.len() == 0 { 0 } else { s[0] + sum_seq(s.subrange(1, s.len() as int)) }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Added lemma to prove sum equivalence */
proof fn lemma_sum_append(s: Seq<int>, v: int)
    ensures sum_seq(s.push(v)) == sum_seq(s) + v
    decreases s.len()
{
    if s.len() == 0 {
        assert(s.push(v) =~= seq![v]);
    } else {
        assert(s.push(v).subrange(1, s.push(v).len() as int) =~= s.subrange(1, s.len() as int).push(v));
        lemma_sum_append(s.subrange(1, s.len() as int), v);
    }
}
// </vc-helpers>

// <vc-spec>
fn solve(n: i8, heights: Vec<i8>) -> (result: Vec<i8>)
    requires 
        valid_input(n as int, heights@.map(|i, v| v as int))
    ensures 
        valid_output(n as int, result@.map(|i, v| v as int)) &&
        sum_seq(result@.map(|i, v| v as int)) == sum_seq(heights@.map(|i, v| v as int)) &&
        is_stable(result@.map(|i, v| v as int))
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed type issues in proof blocks */
    let mut result: Vec<i8> = Vec::new();
    let mut total: i64 = 0;
    let mut i: usize = 0;
    
    // First loop: calculate total sum
    while i < n as usize
        invariant
            0 <= i <= n as int,
            heights.len() == n as int,
            i <= heights.len(),
            total == sum_seq(heights@.take(i as int).map(|j, v| v as int)),
        decreases n as int - i as int
    {
        proof {
            assert(heights@.take((i + 1) as int) =~= heights@.take(i as int).push(heights@[i as int]));
            lemma_sum_append(heights@.take(i as int).map(|j, v| v as int), heights@[i as int] as int);
        }
        total = total + heights[i] as i64;
        i = i + 1;
    }
    
    proof {
        assert(heights@.take(n as int) =~= heights@);
    }
    
    let avg = total / (n as i64);
    let remainder = total % (n as i64);
    
    // Second loop: build result
    i = 0;
    while i < n as usize
        invariant
            0 <= i <= n as int,
            result.len() == i,
            avg >= 0,
            0 <= remainder < n as int,
            total == avg * (n as int) + remainder,
            forall|j: int| 0 <= j < i ==> 0 <= #[trigger] result@[j] as int,
            forall|j: int| 0 <= j < i ==> #[trigger] result@[j] as int == if j < (n as int - remainder as int) { avg as int } else { (avg + 1) as int },
            sum_seq(result@.map(|j, v| v as int)) == if i <= (n as int - remainder as int) { i * avg as int } else { (n as int - remainder as int) * avg as int + (i - (n as int - remainder as int)) * (avg + 1) as int },
        decreases n as int - i as int
    {
        if i < n as usize - (remainder as usize) {
            result.push(avg as i8);
            proof {
                assert(result@.take(i as int).push(avg as i8) =~= result@);
                lemma_sum_append(result@.take(i as int).map(|j, v| v as int), avg as int);
            }
        } else {
            result.push((avg + 1) as i8);
            proof {
                assert(result@.take(i as int).push((avg + 1) as i8) =~= result@);
                lemma_sum_append(result@.take(i as int).map(|j, v| v as int), (avg + 1) as int);
            }
        }
        i = i + 1;
    }
    
    proof {
        assert(sum_seq(result@.map(|j, v| v as int)) == (n as int - remainder as int) * avg as int + remainder as int * (avg + 1) as int);
        assert((n as int - remainder as int) * avg as int + remainder as int * (avg + 1) as int == n as int * avg as int + remainder as int);
        assert(n as int * avg as int + remainder as int == total as int);
        assert(total as int == sum_seq(heights@.map(|j, v| v as int)));
    }
    
    result
}
// </vc-code>


}

fn main() {}