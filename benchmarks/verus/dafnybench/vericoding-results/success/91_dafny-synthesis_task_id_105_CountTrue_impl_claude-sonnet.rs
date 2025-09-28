use vstd::prelude::*;

verus! {

spec fn count_to(a: &[bool], n: int) -> int
    decreases n when 0 <= n <= a.len()
{
    if n <= 0 { 
        0int 
    } else { 
        count_to(a, n - 1) + if a[n - 1] { 1int } else { 0int } 
    }
}

// <vc-helpers>
proof fn count_to_monotonic(a: &[bool], i: int, j: int)
    requires 0 <= i <= j <= a.len()
    ensures count_to(a, i) <= count_to(a, j)
    decreases j - i
{
    if i < j {
        count_to_monotonic(a, i, j - 1);
    }
}

proof fn count_to_bounds(a: &[bool], n: int)
    requires 0 <= n <= a.len()
    ensures 0 <= count_to(a, n) <= n
    decreases n
{
    if n > 0 {
        count_to_bounds(a, n - 1);
    }
}
// </vc-helpers>

// <vc-spec>
fn count_true(a: &[bool]) -> (result: usize)
    ensures result == count_to(a, a.len() as int)
// </vc-spec>
// <vc-code>
{
    let mut count = 0usize;
    let mut i = 0usize;
    
    proof {
        count_to_bounds(a, a.len() as int);
    }
    
    while i < a.len()
        invariant 
            0 <= i <= a.len(),
            count == count_to(a, i as int),
            count <= i
        decreases a.len() - i
    {
        if a[i] {
            count = count + 1;
        }
        
        assert(count_to(a, (i + 1) as int) == count_to(a, i as int) + if a[i as int] { 1int } else { 0int });
        
        i = i + 1;
    }
    
    count
}
// </vc-code>

fn main() {
}

}