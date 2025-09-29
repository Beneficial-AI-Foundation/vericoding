// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn decode_cyclic(s: &Vec<i8>) -> (res: Vec<i8>)
    ensures 
        s.len() == res.len(),
        forall|i: int| s@.len() - s@.len() % 3 <= i < s@.len() ==> res@[i] == s@[i],
        forall|i: int| 0 <= i < s@.len() - s@.len() % 3 ==> (i % 3 == 0 ==> res@[i] == s@[i + 2]),
        forall|i: int| 0 <= i < s@.len() - s@.len() % 3 ==> (i % 3 == 1 ==> res@[i] == s@[i - 1])
// </vc-spec>
// <vc-code>
{
    let n = s.len();
    let mut res = s.clone();
    let mut i: usize = 0;
    let len_prefix = n - n % 3;
    while i < len_prefix
        invariant
            0 <= i <= len_prefix,
            i % 3 == 0,
            res.len() == s.len(),
            len_prefix == s.len() - s.len() % 3,
            forall|j: int| 0 <= j < i && j % 3 == 0 ==> res@[j] == s@[j + 2],
            forall|j: int| 0 <= j < i && j % 3 == 1 ==> res@[j] == s@[j - 1],
            forall|j: int| 0 <= j < i && j % 3 == 2 ==> res@[j] == s@[j],
            forall|j: int| i <= j < s.len() ==> res@[j] == s@[j],
        decreases len_prefix - i
    {
        assert(i + 2 < s.len());
        res.set(i, s[i + 2]);
        res.set(i + 1, s[i]);
        i = i + 3;
    }
    res
}
// </vc-code>


}

fn main() {}