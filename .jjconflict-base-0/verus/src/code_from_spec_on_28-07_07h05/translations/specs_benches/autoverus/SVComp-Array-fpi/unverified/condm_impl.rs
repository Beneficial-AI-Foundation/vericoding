/* code modified by LLM (iteration 1): Fixed Verus specification syntax by moving requires/ensures into proper specification blocks */
pub fn myfun(a: &mut Vec<i32>, N: i32)
    requires
        N > 0,
        old(a).len() == N,
    ensures
        forall |k:int| 0 <= k < N ==> a[k] % 2 == N % 2,
{
    let mut i: usize = 0;
    while i < a.len()
        invariant
            i <= a.len(),
            a.len() == N,
            forall |k:int| 0 <= k < i ==> a[k] % 2 == N % 2,
        /* code modified by LLM (iteration 1): added decreases clause to prove loop termination */
        decreases a.len() - i
    {
        if a[i] % 2 != N % 2 {
            if N % 2 == 0 {
                if a[i] % 2 == 1 {
                    /* code modified by LLM (iteration 1): direct assignment instead of using set method */
                    a[i] = a[i] - 1;
                }
            } else {
                if a[i] % 2 == 0 {
                    /* code modified by LLM (iteration 1): direct assignment instead of using set method */
                    a[i] = a[i] + 1;
                }
            }
        }
        i += 1;
    }
}