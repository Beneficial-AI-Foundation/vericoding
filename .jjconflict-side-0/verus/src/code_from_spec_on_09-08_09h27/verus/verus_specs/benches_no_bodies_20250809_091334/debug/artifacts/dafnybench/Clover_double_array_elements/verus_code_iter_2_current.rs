use vstd::prelude::*;

verus! {
    fn double_array_elements(s: &mut Vec<i32>)
        requires forall|i: int| 0 <= i < old(s).len() ==> #[trigger] old(s)[i] >= -1073741824 && old(s)[i] <= 1073741823, // prevent overflow
        ensures 
            forall|i: int| 0 <= i < old(s).len() ==> #[trigger] s[i] == 2 * old(s)[i],
            s.len() == old(s).len(),
    {
        let mut i = 0;
        while i < s.len()
            invariant 
                0 <= i <= s.len(),
                s.len() == old(s).len(),
                forall|j: int| 0 <= j < i ==> #[trigger] s[j] == 2 * old(s)[j],
                forall|j: int| i <= j < s.len() ==> #[trigger] s[j] == old(s)[j],
                forall|j: int| 0 <= j < s.len() ==> old(s)[j] >= -1073741824 && old(s)[j] <= 1073741823,
        {
            /* code modified by LLM (iteration 1): Store value in temporary to avoid borrow conflict */
            let val = s[i];
            s.set(i, 2 * val);
            i += 1;
        }
    }
}

fn main() {}