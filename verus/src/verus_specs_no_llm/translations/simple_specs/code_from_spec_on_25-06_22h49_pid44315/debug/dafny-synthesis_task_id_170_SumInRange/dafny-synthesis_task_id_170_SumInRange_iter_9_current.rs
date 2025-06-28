use builtin::*;
use builtin_macros::*;

verus! {

spec fn sumTo(a: Vec<int>, start: int, end: int) -> int {
    decreases end - start when start < end
    if start >= end {
        0
    } else if start < 0 || start >= a.len() {
        0  // Handle out-of-bounds gracefully
    } else {
        a[start] + sumTo(a, start + 1, end)
    }
}

proof fn lemma_sumTo_step(a: Vec<int>, start: int, end: int)
    requires
        start < end,
        0 <= start < a.len(),
        start + 1 <= end
    ensures
        sumTo(a, start, end) == a[start] + sumTo(a, start + 1, end)
{
    // This follows directly from the definition of sumTo
}

// Helper lemma to prove the extension property
proof fn lemma_sumTo_extend(a: Vec<int>, start: int, mid: int, end: int)
    requires
        start <= mid <= end,
        0 <= start <= a.len(),
        0 <= mid <= a.len(),
        0 <= end <= a.len()
    ensures
        sumTo(a, start, end) == sumTo(a, start, mid) + sumTo(a, mid, end)
{
    decreases mid - start when start < mid
    if start >= mid {
        // Base case: sumTo(a, start, start) == 0
        assert(sumTo(a, start, mid) == 0);
        assert(sumTo(a, start, end) == sumTo(a, mid, end));
    } else if start >= a.len() {
        // Out of bounds case
        assert(sumTo(a, start, mid) == 0);
        assert(sumTo(a, start, end) == 0);
        assert(sumTo(a, mid, end) == 0);
    } else {
        // Recursive case
        lemma_sumTo_extend(a, start + 1, mid, end);
        // Now we have: sumTo(a, start + 1, end) == sumTo(a, start + 1, mid) + sumTo(a, mid, end)
        // We need to show: sumTo(a, start, end) == sumTo(a, start, mid) + sumTo(a, mid, end)
        // Since sumTo(a, start, end) = a[start] + sumTo(a, start + 1, end)
        // and sumTo(a, start, mid) = a[start] + sumTo(a, start + 1, mid)
        assert(sumTo(a, start, end) == a[start] + sumTo(a, start + 1, end));
        assert(sumTo(a, start, mid) == a[start] + sumTo(a, start + 1, mid));
        assert(sumTo(a, start + 1, end) == sumTo(a, start + 1, mid) + sumTo(a, mid, end));
        assert(sumTo(a, start, end) == a[start] + sumTo(a, start + 1, mid) + sumTo(a, mid, end));
        assert(sumTo(a, start, end) == sumTo(a, start, mid) + sumTo(a, mid, end));
    }
}

// Helper lemma to show that sumTo for a single element equals that element
proof fn lemma_sumTo_single(a: Vec<int>, i: int)
    requires
        0 <= i < a.len()
    ensures
        sumTo(a, i, i + 1) == a[i]
{
    // Follows directly from definition: sumTo(a, i, i+1) = a[i] + sumTo(a, i+1, i+1) = a[i] + 0
    assert(sumTo(a, i + 1, i + 1) == 0);
    assert(sumTo(a, i, i + 1) == a[i] + sumTo(a, i + 1, i + 1));
}

fn SumInRange(a: Vec<int>, start: int, end: int) -> (sum: int)
    requires
        0 <= start && start <= end && end <= a.len()
    ensures
        sum == sumTo(a, start, end)
{
    let mut i = start;
    let mut sum = 0;
    
    while i < end
        invariant
            start <= i <= end,
            sum == sumTo(a, start, i),
            0 <= start <= a.len(),
            0 <= end <= a.len()
    {
        // Prove that adding a[i] extends the sum correctly
        proof {
            lemma_sumTo_single(a, i);
            lemma_sumTo_extend(a, start, i, i + 1);
            assert(sumTo(a, start, i + 1) == sumTo(a, start, i) + sumTo(a, i, i + 1));
            assert(sumTo(a, i, i + 1) == a[i]);
            assert(sumTo(a, start, i + 1) == sum + a[i]);
        }
        
        // Need to convert i to usize for array access
        assert(0 <= i < a.len());
        sum = sum + a[i as usize];
        i = i + 1;
    }
    
    sum
}

fn main() {
}

}