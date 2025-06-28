use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn is_prefix_sum_for(a: Vec<int>, c: Vec<int>) -> bool {
    forall|i: int| 0 <= i < a.len() ==> c.spec_index(i+1) == c.spec_index(i) + a.spec_index(i)
}

spec fn sum(a: Vec<int>, i: int, j: int) -> int 
    decreases j - i
{
    if i >= j {
        0
    } else {
        a.spec_index(i) + sum(a, i + 1, j)
    }
}

fn queryFast(a: Vec<int>, c: Vec<int>, i: int, j: int) -> (r: int)
    requires
        a.len() + 1 == c.len() && c.spec_index(0) == 0,
        0 <= i <= j <= a.len(),
        is_prefix_sum_for(a, c)
    ensures
        r == sum(a, i, j)
{
    proof {
        lemma_prefix_sum_property(a, c, i, j);
    }
    c.spec_index(j) - c.spec_index(i)
}

proof fn lemma_prefix_sum_property(a: Vec<int>, c: Vec<int>, i: int, j: int)
    requires
        a.len() + 1 == c.len() && c.spec_index(0) == 0,
        0 <= i <= j <= a.len(),
        is_prefix_sum_for(a, c)
    ensures
        c.spec_index(j) - c.spec_index(i) == sum(a, i, j)
    decreases j - i
{
    if i >= j {
        // Base case: empty range
    } else {
        // Inductive step
        lemma_prefix_sum_property(a, c, i + 1, j);
        assert(c.spec_index(i+1) == c.spec_index(i) + a.spec_index(i));
        assert(c.spec_index(j) - c.spec_index(i+1) == sum(a, i + 1, j));
        assert(c.spec_index(j) - c.spec_index(i) == 
               (c.spec_index(j) - c.spec_index(i+1)) + (c.spec_index(i+1) - c.spec_index(i)));
        assert(c.spec_index(j) - c.spec_index(i) == 
               sum(a, i + 1, j) + a.spec_index(i));
        assert(sum(a, i, j) == a.spec_index(i) + sum(a, i + 1, j));
    }
}

}