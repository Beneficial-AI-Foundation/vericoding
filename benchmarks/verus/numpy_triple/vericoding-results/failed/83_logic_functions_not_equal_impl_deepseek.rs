// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
proof fn equal_implies_all_false<T>(x1: Seq<T>, x2: Seq<T>, result: Seq<bool>)
    requires x1.len() == x2.len() && x1.len() == result.len(),
    ensures (x1 == x2) ==> (forall|i: int| 0 <= i < result.len() ==> result[i] == false)
{
    if x1 == x2 {
        assert forall|i: int| 0 <= i < result.len() implies result[i] == false by {
            assert(result[i] == (x1[i] != x2[i]));
            assert(x1[i] == x2[i]);
        };
    }
}

proof fn inequality_commutative<T>(result_index: bool, x1_elem: T, x2_elem: T)
    ensures result_index == (x2_elem != x1_elem)
{
    assert((x1_elem != x2_elem) <==> (x2_elem != x1_elem));
}
// </vc-helpers>

// <vc-spec>
fn numpy_not_equal<T: PartialEq>(x1: Vec<T>, x2: Vec<T>) -> (result: Vec<bool>)
    requires x1.len() == x2.len(),
    ensures
        result.len() == x1.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i] == (x1[i] != x2[i]),

        (x1@ == x2@) ==> (forall|i: int| 0 <= i < result.len() ==> result[i] == false),

        forall|i: int| 0 <= i < result.len() ==> result[i] == (x2[i] != x1[i]),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed compilation error by removing @ operator */
    let mut result = Vec::new();
    let mut i = 0;
    
    while i < x1.len()
        invariant
            i >= 0,
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result[j] == (x1[j] != x2[j]),
        decreases x1.len() - i,
    {
        let elem1 = x1[i];
        let elem2 = x2[i];
        result.push(elem1 != elem2);
        i = i + 1;
    }
    
    let result_seq = result.view();
    
    proof {
        equal_implies_all_false(x1.view(), x2.view(), result_seq);
        
        assert forall|i: int| 0 <= i < result_seq.len() implies result_seq[i] == (x2[i] != x1[i]) by {
            inequality_commutative(result_seq[i], x1[i], x2[i]);
        };
    }
    
    result
}
// </vc-code>

}
fn main() {}