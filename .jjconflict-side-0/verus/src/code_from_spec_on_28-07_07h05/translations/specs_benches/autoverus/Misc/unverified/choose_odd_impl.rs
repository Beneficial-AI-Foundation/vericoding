use vstd::prelude::*;
fn main() {}

verus!{
fn choose_odd(v: &Vec<u64>) -> (odd_index: usize)
    requires    
        exists |q:int| 0 <= q < v.len() && v[q] % 2 == 1
    ensures
        odd_index < v.len()
{
    let mut i = 0;
    /* code modified by LLM (iteration 1): added decreases clause to prove loop termination */
    while i < v.len()
        invariant
            0 <= i <= v.len(),
            forall |j:int| 0 <= j < i ==> v[j] % 2 == 0,
        decreases v.len() - i
    {
        if v[i] % 2 == 1 {
            return i;
        }
        i += 1;
    }
    /* code modified by LLM (iteration 1): removed unreachable!() as it's not supported in Verus and added proof that this case is impossible */
    // This point is unreachable because:
    // - The precondition guarantees there exists an odd element at some index q
    // - The loop invariant states all elements from 0 to i-1 are even
    // - When the loop exits, i == v.len(), so all elements are even
    // - This contradicts the precondition
    proof {
        assert(i == v.len());
        assert(forall |j:int| 0 <= j < i ==> v[j] % 2 == 0);
        assert(forall |j:int| 0 <= j < v.len() ==> v[j] % 2 == 0);
        // This contradicts the precondition that there exists an odd element
        assert(false);
    }
    0 // This line will never be reached
}
}