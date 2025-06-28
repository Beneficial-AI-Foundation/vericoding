use builtin::*;
use builtin_macros::*;

verus! {

spec fn sumTo(a: Vec<int>, start: int, end: int) -> int
    decreases end - start
{
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
    decreases end - start
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
    decreases mid - start
{
    if start >= mid {
        // Base case: sumTo(a, start, start) == 0
        assert(sumTo(a, start, mid) == 0);
    } else {
        // Recursive case
        lemma_sumTo_extend(a, start + 1, mid, end);
    }
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
            0 <= i <= a.len(),
            0 <= end <= a.len()
        decreases
            end - i
    {
        // Prove that adding a[i] extends the sum correctly
        proof {
            lemma_sumTo_extend(a, start, i, i + 1);
            assert(sumTo(a, start, i + 1) == sumTo(a, start, i) + sumTo(a, i, i + 1));
            assert(sumTo(a, i, i + 1) == a[i]);
            assert(sumTo(a, start, i + 1) == sumTo(a, start, i) + a[i]);
        }
        
        sum = sum + a[i as usize];
        i = i + 1;
    }
    
    sum
}

fn main() {
}

}