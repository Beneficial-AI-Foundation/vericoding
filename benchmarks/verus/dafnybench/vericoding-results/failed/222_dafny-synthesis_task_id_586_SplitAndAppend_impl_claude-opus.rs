use vstd::prelude::*;

verus! {

// <vc-helpers>
// No additional helpers needed for this implementation
// </vc-helpers>

// <vc-spec>
fn split_and_append(l: Seq<int>, n: int) -> (r: Seq<int>)
    requires 
        n >= 0 && n < l.len(),
    ensures 
        r.len() == l.len(),
        forall|i: int| 0 <= i < l.len() ==> r[i] == l[((i + n) as nat % l.len()) as int],
// </vc-spec>
// <vc-code>
{
    let first_part = l.subrange(0, n);
    let second_part = l.subrange(n, l.len() as int);
    let result = second_part.add(first_part);
    
    proof {
        // Prove that result has the correct length
        assert(result.len() == second_part.len() + first_part.len());
        assert(second_part.len() == l.len() - n);
        assert(first_part.len() == n);
        assert(result.len() == l.len());
        
        // Prove that each element is in the correct position
        assert forall|i: int| 0 <= i < l.len() implies result[i] == l[((i + n) as nat % l.len()) as int] by {
            if i < l.len() - n {
                // Element comes from second_part
                assert(result[i] == second_part[i]);
                assert(second_part[i] == l[i + n]);
                assert(((i + n) as nat % l.len()) as int == i + n);
            } else {
                // Element comes from first_part
                let idx = i - (l.len() - n);
                assert(result[i] == first_part[idx]);
                assert(first_part[idx] == l[idx]);
                assert(idx == i + n - l.len());
                assert(((i + n) as nat % l.len()) as int == i + n - l.len());
            }
        }
    }
    
    result
}
// </vc-code>

fn main() {
}

}