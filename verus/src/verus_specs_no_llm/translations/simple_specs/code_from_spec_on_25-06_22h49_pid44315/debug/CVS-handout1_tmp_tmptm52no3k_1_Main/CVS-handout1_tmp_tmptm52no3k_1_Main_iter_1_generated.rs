use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

// Specification function to check if c is a prefix sum of a
spec fn is_prefix_sum_for(a: Vec<int>, c: Vec<int>) -> bool {
    c.len() == a.len() + 1 &&
    c[0] == 0 &&
    (forall|i: int| 0 <= i < a.len() ==> c[i as nat + 1] == c[i as nat] + a[i as nat])
}

// Helper function to compute sum of array elements from start to end (exclusive)
fn sum(x: &Vec<int>, start: usize, end: usize) -> (result: int)
    requires
        start <= end,
        end <= x.len(),
    ensures
        result == sum_spec(x@, start as int, end as int),
{
    let mut total = 0;
    let mut i = start;
    
    while i < end
        invariant
            start <= i <= end,
            end <= x.len(),
            total == sum_spec(x@, start as int, i as int),
    {
        total = total + x[i];
        i = i + 1;
    }
    
    total
}

// Specification function for sum computation
spec fn sum_spec(x: Seq<int>, start: int, end: int) -> int
    decreases end - start
{
    if start >= end {
        0
    } else {
        x[start] + sum_spec(x, start + 1, end)
    }
}

// Main method that demonstrates the functionality
fn Main() -> (result: bool)
    ensures result == true,
{
    // Create and initialize array x
    let mut x = Vec::new();
    x.push(2);
    x.push(2);
    x.push(1);
    x.push(5);
    
    // Compute sum
    let y = sum(&x, 0, x.len());
    assert(y == 10);
    
    // Create prefix sum array c
    let mut c = Vec::new();
    c.push(0);  // c[0] = 0
    c.push(2);  // c[1] = 0 + 2 = 2
    c.push(4);  // c[2] = 2 + 2 = 4  
    c.push(5);  // c[3] = 4 + 1 = 5
    c.push(10); // c[4] = 5 + 5 = 10
    
    // Verify that c is indeed a prefix sum of x
    assert(is_prefix_sum_for(x, c));
    
    true
}

// Lemma to help prove properties about sum_spec
proof fn lemma_sum_spec_additive(x: Seq<int>, start: int, mid: int, end: int)
    requires
        start <= mid <= end,
        0 <= start,
        end <= x.len(),
    ensures
        sum_spec(x, start, end) == sum_spec(x, start, mid) + sum_spec(x, mid, end),
    decreases end - start
{
    if start < mid {
        lemma_sum_spec_additive(x, start + 1, mid, end);
    }
}

}