use vstd::prelude::*;

verus! {
    fn append(a: &[int], b: int) -> (c: Vec<int>)
        requires a.len() < usize::MAX
        ensures c@ == a@ + seq![b]
    {
        let mut result = Vec::new();
        let mut i = 0;
        /* code modified by LLM (iteration 1): added decreases clause to prove loop termination */
        while i < a.len()
            invariant 
                i <= a.len(),
                result@ == a@.subrange(0, i as int)
            decreases a.len() - i
        {
            result.push(a[i]);
            i += 1;
        }
        result.push(b);
        result
    }
}

fn main() {}