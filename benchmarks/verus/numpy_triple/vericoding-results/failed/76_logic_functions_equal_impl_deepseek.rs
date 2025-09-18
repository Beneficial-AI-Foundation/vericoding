// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
proof fn element_equal_implies_equal<T>(s1: Seq<T>, s2: Seq<T>)
    requires s1 =~= s2,
    ensures forall|i: int| 0 <= i < s1.len() ==> s1[i] == s2[i]
{
    assert forall|i: int| 0 <= i < s1.len() implies s1[i] == s2[i] by {
        assert(s1 =~= s2);
    };
}
// </vc-helpers>

// <vc-spec>
fn numpy_equal<T>(x1: Vec<T>, x2: Vec<T>) -> (result: Vec<bool>)
    requires 
        x1.len() == x2.len(),
    ensures
        result.len() == x1.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i] == (x1[i] == x2[i]),
        forall|i: int| 0 <= i < result.len() ==> (result[i] == true || result[i] == false),
        x1@ == x2@ ==> forall|i: int| 0 <= i < result.len() ==> result[i] == true
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): fixed proof function syntax */
{
    let len = x1.len();
    assert(x2.len() == len);
    
    let mut result: Vec<bool> = Vec::new();
    let mut n: usize = 0;
    
    while n < len
        invariant
            n <= len,
            result.len() == n,
            forall|i: int| 0 <= i < n ==> result[i] == (x1[i] == x2[i]),
            forall|i: int| 0 <= i < n ==> (result[i] == true || result[i] == false)
        decreases len - n
    {
        let elem_equal = x1[n] == x2[n];
        result.push(elem_equal);
        n = n + 1;
    }
    
    proof {
        element_equal_implies_equal(x1@, x2@);
    }
    
    result
}
// </vc-code>

}
fn main() {}