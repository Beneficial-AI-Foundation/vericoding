use vstd::prelude::*;

verus! {
    fn append(a: &[int], b: int) -> (c: Vec<int>)
        requires a.len() < usize::MAX
        ensures c@ == a@ + seq![b]
    {
        let mut result = Vec::new();
        
        // Copy all elements from a
        for i in 0..a.len()
            invariant result@ == a@.subrange(0, i as int)
        {
            result.push(a[i]);
        }
        
        // Add b at the end
        result.push(b);
        
        result
    }
}

fn main() {}