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

// Helper lemma to prove sum_spec for specific sequences
proof fn lemma_sum_spec_concrete(x: Seq<int>)
    requires x.len() == 4,
    requires x[0] == 2 && x[1] == 2 && x[2] == 1 && x[3] == 5,
    ensures sum_spec(x, 0, 4) == 10,
{
    assert(sum_spec(x, 0, 4) == x[0] + sum_spec(x, 1, 4));
    assert(sum_spec(x, 1, 4) == x[1] + sum_spec(x, 2, 4));
    assert(sum_spec(x, 2, 4) == x[2] + sum_spec(x, 3, 4));
    assert(sum_spec(x, 3, 4) == x[3] + sum_spec(x, 4, 4));
    assert(sum_spec(x, 4, 4) == 0);
}

// Helper lemma to prove prefix sum property for concrete vectors
proof fn lemma_prefix_sum_concrete(x: Vec<int>, c: Vec<int>)
    requires 
        x.len() == 4,
        c.len() == 5,
        x[0] == 2 && x[1] == 2 && x[2] == 1 && x[3] == 5,
        c[0] == 0 && c[1] == 2 && c[2] == 4 && c[3] == 5 && c[4] == 10,
    ensures is_prefix_sum_for(x, c),
{
    assert(c.len() == x.len() + 1);
    assert(c[0] == 0);
    
    // Prove each prefix sum relationship individually
    assert(c[1] == c[0] + x[0]); // 2 == 0 + 2
    assert(c[2] == c[1] + x[1]); // 4 == 2 + 2  
    assert(c[3] == c[2] + x[2]); // 5 == 4 + 1
    assert(c[4] == c[3] + x[3]); // 10 == 5 + 5
    
    // This proves the forall condition
    assert forall|i: int| 0 <= i < x.len() implies c[i as nat + 1] == c[i as nat] + x[i as nat] by {
        if i == 0 {
            assert(c[1] == c[0] + x[0]);
        } else if i == 1 {
            assert(c[2] == c[1] + x[1]);
        } else if i == 2 {
            assert(c[3] == c[2] + x[2]);
        } else if i == 3 {
            assert(c[4] == c[3] + x[3]);
        }
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
    
    // Prove properties about the concrete sequence
    proof {
        lemma_sum_spec_concrete(x@);
    }
    
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
    
    // Prove the prefix sum property
    proof {
        lemma_prefix_sum_concrete(x, c);
    }
    
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