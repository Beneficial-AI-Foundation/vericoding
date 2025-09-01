use vstd::prelude::*;

verus! {

// <vc-helpers>
// No additional helpers needed for this implementation
// </vc-helpers>

// <vc-spec>
fn reverse(a: &[i32]) -> (result: Vec<i32>)
    // post-conditions-start
    ensures
        result.len() == a.len(),
        forall|i: int| 0 <= i && i < result.len() ==> result[i] == a[a.len() - 1 - i],
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    let n = a.len();
    let mut result: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    
    while i < n
        invariant
            i <= n,
            n == a.len(),
            result.len() == i,
            forall|j: int| 0 <= j && j < i ==> result[j] == a@[(n - 1 - j) as int],
        decreases n - i,
    {
        // Prove that n - 1 - i is a valid index
        assert(i < n);
        assert(n >= 1) by {
            assert(i < n);
            assert(i >= 0);
        }
        assert(n - 1 >= i);
        assert(n - 1 - i >= 0);
        assert(n - 1 - i < n) by {
            assert(i >= 0);
        }
        
        result.push(a[(n - 1 - i) as usize]);
        
        assert(result.len() == i + 1);
        assert(result[i as int] == a@[(n - 1 - i) as int]);
        
        i = i + 1;
    }
    
    result
}
// </vc-code>

fn main() {}
}