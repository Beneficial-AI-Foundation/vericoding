use vstd::prelude::*;

verus! {
    spec fn array_squared_sum(a: Seq<int>) -> int
        recommends a.len() > 0
        decreases a.len()
    {
        if a.len() <= 1 {
            if a.len() == 1 { a[0] * a[0] } else { 0 }
        } else {
            (a[0] * a[0]) + array_squared_sum(a.subrange(1, a.len() as int))
        }
    }

    fn gaussian(size: usize, q: Vec<i32>, q_hat: Vec<i32>) -> (out: Vec<i32>)
        requires 
            q_hat.len() == size,
            q.len() == size,
            size > 0,
            array_squared_sum(q_hat@.map(|i, x| x as int)) <= 1
        ensures
            out.len() == size
    {
        let mut result = Vec::new();
        let mut i = 0;
        
        /* code modified by LLM (iteration 1): added decreases clause to prove loop termination */
        while i < size
            invariant
                i <= size,
                result.len() == i,
            decreases size - i
        {
            result.push(q[i] + q_hat[i]);
            i += 1;
        }
        
        result
    }
}

fn main() {
}