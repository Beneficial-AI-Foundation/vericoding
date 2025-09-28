use vstd::prelude::*;

verus! {

// Given an array of integers, it returns the sum. [1,3,3,2]->9

spec fn sum(xs: Seq<i32>) -> int
    decreases xs.len()
{
    if xs.len() == 0 {
        0int
    } else {
        sum(xs.subrange(0, xs.len() - 1)) + xs[xs.len() - 1] as int
    }
}

// <vc-helpers>
proof fn sum_subrange_lemma(xs: Seq<i32>, i: int)
    requires 0 <= i <= xs.len()
    ensures sum(xs.subrange(0, i)) == if i == 0 { 0 } else { sum(xs.subrange(0, i - 1)) + xs[i - 1] as int }
    decreases i
{
    if i == 0 {
        assert(xs.subrange(0, 0).len() == 0);
    } else {
        assert(xs.subrange(0, i).len() == i);
        assert(xs.subrange(0, i)[i - 1] == xs[i - 1]);
    }
}

proof fn sum_iterative_correctness(xs: Seq<i32>, i: int, acc: int)
    requires 0 <= i <= xs.len()
    requires acc == sum(xs.subrange(0, i))
    ensures acc + sum(xs.subrange(i, xs.len())) == sum(xs)
    decreases xs.len() - i
{
    if i == xs.len() {
        assert(xs.subrange(i, xs.len()).len() == 0);
        assert(xs.subrange(0, xs.len()) == xs);
    } else {
        sum_subrange_lemma(xs, i + 1);
        assert(xs.subrange(0, i + 1) == xs.subrange(0, i).push(xs[i]));
        sum_iterative_correctness(xs, i + 1, acc + xs[i] as int);
    }
}
// </vc-helpers>

// <vc-spec>
fn sum_array(xs: &[i32]) -> (s: i32)
    ensures s as int == sum(xs@)
// </vc-spec>
// <vc-code>
{
    let mut s: i32 = 0;
    let mut i: usize = 0;
    
    while i < xs.len()
        invariant 
            0 <= i <= xs.len(),
            s as int == sum(xs@.subrange(0, i as int))
    {
        proof {
            sum_subrange_lemma(xs@, i as int + 1);
        }
        s = s + xs[i];
        i = i + 1;
    }
    
    proof {
        assert(i == xs.len());
        assert(xs@.subrange(0, i as int) == xs@);
    }
    
    s
}
// </vc-code>

fn main() {
}

}