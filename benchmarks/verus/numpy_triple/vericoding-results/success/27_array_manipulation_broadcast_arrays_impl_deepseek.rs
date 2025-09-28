// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

proof fn proof_broadcast_a_len_1(a: Vec<i8>, max_len: usize, i: int, a_broadcast: Vec<i8>) 
    requires 
        a.len() == 1,
        0 <= i < max_len as int,
        a_broadcast.len() == max_len,
        forall|j: int| 0 <= j < max_len as int ==> a_broadcast[j] == a[0]
    ensures
        a_broadcast[i] == a[0]
{
    /* The forall quantifier in the precondition guarantees this */
}

proof fn proof_broadcast_b_len_1(b: Vec<i8>, max_len: usize, i: int, b_broadcast: Vec<i8>) 
    requires 
        b.len() == 1,
        0 <= i < max_len as int,
        b_broadcast.len() == max_len,
        forall|j: int| 0 <= j < max_len as int ==> b_broadcast[j] == b[0]
    ensures
        b_broadcast[i] == b[0]
{
    /* The forall quantifier in the precondition guarantees this */
}

proof fn proof_preserve_elements_a_same_len(a: Vec<i8>, a_broadcast: Vec<i8>) 
    requires 
        a_broadcast.len() == a.len(),
        forall|i: int| 0 <= i < a.len() as int ==> a_broadcast[i] == a[i]
    ensures
        forall|i: int| 0 <= i < a.len() as int ==> a_broadcast[i] == a[i]
{
    /* Directly follows from the precondition */
}

proof fn proof_preserve_elements_b_same_len(b: Vec<i8>, b_broadcast: Vec<i8>) 
    requires 
        b_broadcast.len() == b.len(),
        forall|i: int| 0 <= i < b.len() as int ==> b_broadcast[i] == b[i]
    ensures
        forall|i: int| 0 <= i < b.len() as int ==> b_broadcast[i] == b[i]
{
    /* Directly follows from the precondition */
}

fn get_max_len(a_len: usize, b_len: usize) -> (max_len: usize)
    ensures
        max_len >= a_len,
        max_len >= b_len,
        (max_len == a_len) || (max_len == b_len)
{
    if a_len > b_len {
        a_len
    } else {
        b_len
    }
}

fn create_broadcast_single_value(value: i8, len: usize) -> (result: Vec<i8>)
    ensures
        result.len() == len,
        forall|i: int| 0 <= i < len as int ==> result[i] == value
{
    let mut vec = Vec::new();
    let mut i: usize = 0;
    while i < len
        invariant
            i <= len,
            vec.len() == i,
            forall|j: int| 0 <= j < i as int ==> vec[j] == value
        decreases
            len - i
    {
        vec.push(value);
        i = i + 1;
    }
    vec
}

// </vc-helpers>

// <vc-spec>
fn broadcast_arrays(a: Vec<i8>, b: Vec<i8>) -> (result: (Vec<i8>, Vec<i8>))
    requires 
        a.len() == 1 || b.len() == 1 || a.len() == b.len(),
        a.len() > 0,
        b.len() > 0,
    ensures 
        ({
            let (a_broadcast, b_broadcast) = result;
            let max_len = if a.len() > b.len() { a.len() } else { b.len() };
            
            /* Both output arrays have the same size as max(m, n) */
            a_broadcast.len() == max_len &&
            b_broadcast.len() == max_len &&
            
            /* First array broadcasting rules */
            (a.len() == 1 ==> forall|i: int| 0 <= i < max_len as int ==> a_broadcast[i] == a[0]) &&
            (b.len() == 1 && a.len() > 1 ==> forall|i: int| 0 <= i < a.len() as int ==> a_broadcast[i] == a[i]) &&
            (a.len() == b.len() ==> forall|i: int| 0 <= i < a.len() as int ==> a_broadcast[i] == a[i]) &&
            
            /* Second array broadcasting rules */
            (b.len() == 1 ==> forall|i: int| 0 <= i < max_len as int ==> b_broadcast[i] == b[0]) &&
            (a.len() == 1 && b.len() > 1 ==> forall|i: int| 0 <= i < b.len() as int ==> b_broadcast[i] == b[i]) &&
            (a.len() == b.len() ==> forall|i: int| 0 <= i < b.len() as int ==> b_broadcast[i] == b[i])
        })
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): Added decreases clause to while loop */
    let max_len = get_max_len(a.len(), b.len());
    
    let a_broadcast = if a.len() == 1 {
        // Broadcast the single value
        create_broadcast_single_value(a[0], max_len)
    } else if b.len() == 1 {
        // Keep original a array, but verify it's the right length
        assert(a.len() == max_len);
        a.clone()
    } else {
        // a.len() == b.len() - keep original
        assert(a.len() == b.len());
        assert(a.len() == max_len);
        a.clone()
    };
    
    let b_broadcast = if b.len() == 1 {
        // Broadcast the single value
        create_broadcast_single_value(b[0], max_len)
    } else if a.len() == 1 {
        // Keep original b array, but verify it's the right length
        assert(b.len() == max_len);
        b.clone()
    } else {
        // a.len() == b.len() - keep original
        assert(b.len() == max_len);
        b.clone()
    };
    
    (a_broadcast, b_broadcast)
}
// </vc-code>


}
fn main() {}