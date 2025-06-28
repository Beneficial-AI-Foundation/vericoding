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
        // Use the lemma to establish the relationship for the next step
        proof {
            lemma_sumTo_step(a, start, i + 1);
        }
        
        // We need to show that sumTo(a, start, i+1) == sumTo(a, start, i) + a[i]
        // This follows from the definition and our lemma
        assert(sumTo(a, start, i + 1) == a[i] + sumTo(a, i + 1, i + 1)) by {
            // sumTo(a, i+1, i+1) == 0 by definition
            assert(sumTo(a, i + 1, i + 1) == 0);
        };
        assert(sumTo(a, start, i + 1) == sumTo(a, start, i) + a[i]) by {
            // This needs to be proven by the structure of sumTo
            if start == i {
                assert(sumTo(a, start, i) == 0);
                assert(sumTo(a, start, i + 1) == a[start]);
            } else {
                // For the general case, we use induction on the structure
                lemma_sumTo_extend(a, start, i, i + 1);
            }
        };
        
        sum = sum + a[i as usize];
        i = i + 1;
    }
    
    sum
}

// Helper lemma to prove the extension property
proof fn lemma_sumTo_extend(a: Vec<int>, start: int, mid: int, end: int)
    requires
        start <= mid < end,
        0 <= start < a.len(),
        0 <= mid < a.len(),
        end <= a.len()
    ensures
        sumTo(a, start, end) == sumTo(a, start, mid) + sumTo(a, mid, end)
    decreases mid - start
{
    if start == mid {
        // Base case: sumTo(a, start, start) == 0
        assert(sumTo(a, start, mid) == 0);
    } else {
        // Recursive case
        lemma_sumTo_extend(a, start + 1, mid, end);
        assert(sumTo(a, start + 1, end) == sumTo(a, start + 1, mid) + sumTo(a, mid, end));
        assert(sumTo(a, start, end) == a[start] + sumTo(a, start + 1, end));
        assert(sumTo(a, start, mid) == a[start] + sumTo(a, start + 1, mid));
    }
}

fn main() {
}

}