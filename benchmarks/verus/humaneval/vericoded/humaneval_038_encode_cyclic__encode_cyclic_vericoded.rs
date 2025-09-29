// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn encode_cyclic(s: Vec<i8>) -> (res: Vec<i8>)
    ensures 
        s.len() == res.len(),
        forall|i: int| 0 <= i < s@.len() - s@.len() % 3 ==> (i % 3 == 0 ==> res@[i] == s@[i + 1]),
        forall|i: int| 0 <= i < s@.len() - s@.len() % 3 ==> (i % 3 == 1 ==> res@[i] == s@[i + 1]),
        forall|i: int| 0 <= i < s@.len() - s@.len() % 3 ==> (i % 3 == 2 ==> res@[i] == s@[i - 2]),
        forall|i: int| s@.len() - s@.len() % 3 <= i < s@.len() ==> (res@[i] == s@[i])
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): corrected the cyclic shift logic and simplified bounds assertions */
    let mut res = s.clone();
    let n = s.len();
    let limit = n - n % 3;
    let mut i: usize = 0;

    while i < limit
        invariant
            0 <= i <= limit,
            i % 3 == 0,
            res.len() == s.len(),
            n == s.len(),
            limit == n - n % 3,
            forall|j: int| 0 <= j < i ==> (j % 3 == 0 ==> (j + 1 < n && res@[j] == s@[j + 1])),
            forall|j: int| 0 <= j < i ==> (j % 3 == 1 ==> (j + 1 < n && res@[j] == s@[j + 1])),
            forall|j: int| 0 <= j < i ==> (j % 3 == 2 ==> (j - 2 >= 0 && res@[j] == s@[j - 2])),
            forall|j: int| i <= j < s.len() ==> (res@[j] == s@[j]),
        decreases limit - i
    {
        assert(i + 2 < n);

        let s_at_i = s[i];
        let s_at_i_plus_1 = s[i + 1];
        let s_at_i_plus_2 = s[i + 2];

        res.set(i, s_at_i_plus_1);
        res.set(i + 1, s_at_i_plus_2);
        res.set(i + 2, s_at_i);

        i = i + 3;
    }

    res
}
// </vc-code>


}

fn main() {}