// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
proof fn lemma_mod_properties(x: int, y: int)
    requires
        y != 0,
    ensures
        x == (x / y) * y + (x % y),
        -y < x % y < y,
{
    /* helper modified by LLM (iteration 5): fixed modulus properties with proper division/modulus relationship */
    if y > 0 {
        assert(x % y >= 0);
        assert(x % y < y);
    } else {
        assert(x % y <= 0);
        assert(x % y > y);
    }
    assert(x == (x / y) * y + (x % y));
}
// </vc-helpers>

// <vc-spec>
spec fn all_nonzero(v: Seq<i32>) -> bool {
    forall|i: int| 0 <= i < v.len() ==> v[i] != 0
}

fn mod_vec(a: Vec<i32>, b: Vec<i32>) -> (result: Vec<i32>)
    requires 
        a.len() == b.len(),
        all_nonzero(b@),
    ensures
        result.len() == a.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i] == a[i] % b[i],
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed modulus properties usage and index bounds */
    let mut result = Vec::new();
    let mut i: usize = 0;
    
    while i < a.len()
        invariant
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result@[j] == a@[j] % b@[j],
            i <= a.len(),
        decreases a.len() - i,
    {
        assert(i < a.view().len());
        assert(i < b.view().len());
        let a_val = a[i];
        let b_val = b[i];
        
        proof {
            assert(b_val != 0);
            lemma_mod_properties(a_val as int, b_val as int);
        }
        
        result.push(a_val % b_val);
        i = i + 1;
    }
    
    result
}
// </vc-code>


}
fn main() {}