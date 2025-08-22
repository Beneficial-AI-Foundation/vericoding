use vstd::prelude::*;

verus! {
    fn append(a: &[int], b: int) -> (c: Vec<int>)
        requires a.len() < usize::MAX
        ensures c@ == a@ + seq![b]
    {
        let mut c = Vec::new();
        for i in 0..a.len()
            invariant c@ == a@.subrange(0, i as int)
        {
            c.push(a[i]);
        }
        c.push(b);
        c
    }
}

fn main() {}