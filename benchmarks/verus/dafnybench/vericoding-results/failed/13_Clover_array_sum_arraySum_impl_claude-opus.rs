use vstd::prelude::*;

verus! {

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn array_sum(a: &Vec<i32>, b: &Vec<i32>) -> (c: Vec<i32>)
    requires 
        a.len() == b.len(),
    ensures 
        c.len() == a.len(),
        forall|i: int| 0 <= i < a.len() ==> a[i] + b[i] == c[i],
// </vc-spec>
// <vc-code>
{
    let mut c = Vec::new();
    let n = a.len();
    
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            c.len() == i,
            n == a.len(),
            n == b.len(),
            forall|j: int| 0 <= j < i ==> #[trigger] c@[j] == a@[j] + b@[j],
    {
        let sum = a[i] + b[i];
        c.push(sum);
        
        assert(c@[c.len() - 1] == a@[i as int] + b@[i as int]);
        assert(c.len() == i + 1);
        assert(forall|j: int| 0 <= j < i ==> c@[j] == a@[j] + b@[j]);
        assert(c@[i as int] == a@[i as int] + b@[i as int]);
        
        i = i + 1;
    }
    
    c
}
// </vc-code>

fn main() {}

}