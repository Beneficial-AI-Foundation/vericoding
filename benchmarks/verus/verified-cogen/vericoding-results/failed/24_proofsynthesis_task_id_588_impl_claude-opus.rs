// <vc-preamble>
#![verifier::loop_isolation(false)]
use vstd::math::*;
use vstd::prelude::*;

verus! {

spec fn max_rcur(seq: Seq<i32>) -> (result: int)
    decreases seq.len(),
{
    if seq.len() <= 1 {
        seq.first() as int
    } else {
        max(seq.last() as int, max_rcur(seq.drop_last()))
    }
}

spec fn min_rcur(seq: Seq<i32>) -> (result: int)
    decreases seq.len(),
{
    if seq.len() <= 1 {
        seq.first() as int
    } else {
        min(seq.last() as int, min_rcur(seq.drop_last()))
    }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): added lemmas to prove max-min difference is within i32 bounds */
spec fn max_spec(a: int, b: int) -> int { if a >= b { a } else { b } }

spec fn min_spec(a: int, b: int) -> int { if a <= b { a } else { b } }

proof fn lemma_max_rcur_bounds(seq: Seq<i32>, i: int)
    requires
        seq.len() > 0,
        0 <= i < seq.len(),
    ensures
        seq[i] as int <= max_rcur(seq),
    decreases seq.len(),
{
    if seq.len() == 1 {
        assert(seq[0] as int == max_rcur(seq));
    } else if i == seq.len() - 1 {
        assert(seq[i] as int == seq.last() as int);
        assert(max_rcur(seq) == max(seq.last() as int, max_rcur(seq.drop_last())));
    } else {
        lemma_max_rcur_bounds(seq.drop_last(), i);
        assert(seq.drop_last()[i] == seq[i]);
        assert(max_rcur(seq) == max(seq.last() as int, max_rcur(seq.drop_last())));
    }
}

proof fn lemma_min_rcur_bounds(seq: Seq<i32>, i: int)
    requires
        seq.len() > 0,
        0 <= i < seq.len(),
    ensures
        min_rcur(seq) <= seq[i] as int,
    decreases seq.len(),
{
    if seq.len() == 1 {
        assert(seq[0] as int == min_rcur(seq));
    } else if i == seq.len() - 1 {
        assert(seq[i] as int == seq.last() as int);
        assert(min_rcur(seq) == min(seq.last() as int, min_rcur(seq.drop_last())));
    } else {
        lemma_min_rcur_bounds(seq.drop_last(), i);
        assert(seq.drop_last()[i] == seq[i]);
        assert(min_rcur(seq) == min(seq.last() as int, min_rcur(seq.drop_last())));
    }
}

proof fn lemma_max_min_bounds(seq: Seq<i32>)
    requires
        seq.len() > 0,
        forall|i: int| #[trigger] (0 <= i < seq.len()) ==> i32::MIN / 2 < seq[i] < i32::MAX / 2,
    ensures
        i32::MIN / 2 < max_rcur(seq) < i32::MAX / 2,
        i32::MIN / 2 < min_rcur(seq) < i32::MAX / 2,
        i32::MIN < max_rcur(seq) - min_rcur(seq) < i32::MAX,
    decreases seq.len(),
{
    if seq.len() == 1 {
        assert(max_rcur(seq) == seq[0] as int);
        assert(min_rcur(seq) == seq[0] as int);
    } else {
        lemma_max_min_bounds(seq.drop_last());
        assert(max_rcur(seq) == max(seq.last() as int, max_rcur(seq.drop_last())));
        assert(min_rcur(seq) == min(seq.last() as int, min_rcur(seq.drop_last())));
    }
}
// </vc-helpers>

// <vc-spec>
fn difference_max_min(arr: &Vec<i32>) -> (diff: i32)

    requires
        arr.len() > 0,
        forall|i: int| 0 <= i < arr.len() ==> i32::MIN / 2 < #[trigger] arr[i] < i32::MAX / 2,

    ensures
        diff == max_rcur(arr@) - min_rcur(arr@),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed type casting to avoid using int in exec code */
    let mut max_val: i32 = arr[0];
    let mut min_val: i32 = arr[0];
    let mut i: usize = 1;
    
    while i < arr.len()
        invariant
            1 <= i <= arr.len(),
            max_val as int == max_rcur(arr@.take(i as int)),
            min_val as int == min_rcur(arr@.take(i as int)),
            forall|j: int| 0 <= j < i ==> arr[j] as int <= max_val as int,
            forall|j: int| 0 <= j < i ==> min_val as int <= arr[j] as int,
        decreases arr.len() - i,
    {
        proof {
            assert(arr@.take(i as int + 1).drop_last() =~= arr@.take(i as int));
            assert(arr@.take(i as int + 1).last() == arr[i as int]);
            lemma_max_rcur_bounds(arr@.take(i as int + 1), i as int);
            lemma_min_rcur_bounds(arr@.take(i as int + 1), i as int);
        }
        
        if arr[i] > max_val {
            max_val = arr[i];
        }
        if arr[i] < min_val {
            min_val = arr[i];
        }
        i = i + 1;
    }
    
    proof {
        assert(arr@.take(arr.len() as int) =~= arr@);
        lemma_max_min_bounds(arr@);
        assert(i32::MIN < max_rcur(arr@) - min_rcur(arr@) < i32::MAX);
    }
    
    let diff = max_val - min_val;
    diff
}
// </vc-code>

}
fn main() {}