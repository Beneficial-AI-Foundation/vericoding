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
        // Add bounds check assertion to help verification
        assert(0 <= i < a.len());
        
        // Proof hint: before updating sum, establish the relationship
        assert(sumTo(a, start, i + 1) == sumTo(a, start, i) + a[i]);
        
        sum = sum + a[i];
        i = i + 1;
    }
    
    sum
}

fn main() {
}

}