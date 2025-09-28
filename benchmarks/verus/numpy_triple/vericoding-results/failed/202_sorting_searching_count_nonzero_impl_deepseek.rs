// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>


proof fn lemma_vec_index_same_len<T>(v: &Vec<T>) 
    ensures 
        v@.len() == v.len() as int, 
{
}

spec fn all_zero(s: Seq<i8>, start: int, end: int) -> bool {
    forall|i: int| start <= i < end ==> s[i] == 0
}

spec fn some_nonzero(s: Seq<i8>, start: int, end: int) -> bool {
    exists|i: int| start <= i < end && s[i] != 0
}

spec fn count_nonzero_spec(s: Seq<i8>) -> nat {
    s.filter(|x: i8| x != 0).len()
}

proof fn all_zero_implies_count_zero(s: Seq<i8>) 
    requires 
        forall|i: int| 0 <= i < s.len() ==> s[i] == 0,
    ensures 
        count_nonzero_spec(s) == 0, 
{
    assert(s.filter(|x: i8| x != 0).len() == 0);
}

proof fn all_nonzero_implies_count_full(s: Seq<i8>) 
    requires 
        forall|i: int| 0 <= i < s.len() ==> s[i] != 0, 
    ensures 
        count_nonzero_spec(s) == s.len() as nat, 
{
    assert(s.filter(|x: i8| x != 0).len() == s.len());
}

proof fn lemma_len_zero_implies_count_zero(s: Seq<i8>)
    requires
        s.len() == 0,
    ensures
        count_nonzero_spec(s) == 0,
{
}


// </vc-helpers>

// <vc-spec>
fn count_nonzero(a: Vec<i8>) -> (count: usize)
    ensures
        count <= a.len(),
        a.len() == 0 ==> count == 0,
        (forall|i: int| 0 <= i < a@.len() ==> a[i] == 0) ==> count == 0,
        (forall|i: int| 0 <= i < a@.len() ==> a[i] != 0) ==> count == a.len(),
        (exists|i: int| 0 <= i < a@.len() && a[i] != 0) ==> count > 0,
        (exists|i: int| 0 <= i < a@.len() && a[i] == 0) ==> count < a.len()
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed loop invariant with proper type conversion and added proof blocks */
    let mut count: usize = 0;
    let mut index: usize = 0;
    
    while index < a.len()
        invariant
            count == count_nonzero_spec(a@.subrange(0, index as int)) as usize,
            count <= index,
            index <= a.len(),
        decreases a.len() - index
    {
        if a[index] != 0 {
            count = count + 1;
        }
        
        index = index + 1;
    }
    
    proof {
        all_zero_implies_count_zero(a@);
        all_nonzero_implies_count_full(a@);
    }
    
    count
}
// </vc-code>

}
fn main() {}