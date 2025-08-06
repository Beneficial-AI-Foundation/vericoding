use vstd::prelude::*;

verus! {
    fn double_array_elements(s: &mut Vec<i32>)
        requires forall|i: int| 0 <= i < old(s).len() ==> #[trigger] old(s)[i] >= -1073741824 && old(s)[i] <= 1073741823, // prevent overflow
        ensures 
            forall|i: int| 0 <= i < old(s).len() ==> #[trigger] s[i] == 2 * old(s)[i],
            s.len() == old(s).len(),
    {
        let mut i: usize = 0;
        while i < s.len()
            invariant
                i <= s.len(),
                s.len() == old(s).len(),
                forall|j: int| 0 <= j < i ==> s[j] == 2 * old(s)[j],
                forall|j: int| i <= j < s.len() ==> s[j] == old(s)[j],
        {
            /* code modified by LLM (iteration 1): read value first to avoid borrowing conflict */
            let val = s[i];
            s.set(i, 2 * val);
            i += 1;
        }
    }
}

fn main() {}