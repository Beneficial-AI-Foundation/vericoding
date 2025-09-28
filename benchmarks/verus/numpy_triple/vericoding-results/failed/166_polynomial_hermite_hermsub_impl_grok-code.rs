// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn hermsub(c1: Vec<i8>, c2: Vec<i8>) -> (result: Vec<i8>)
    ensures
        result.len() == if c1.len() >= c2.len() { c1.len() } else { c2.len() },
        forall|i: int| 0 <= i < c1.len() && 0 <= i < c2.len() ==> 
            result@[i] == c1@[i] - c2@[i],
        c1.len() > c2.len() ==> forall|i: int| 
            c2.len() <= i < c1.len() ==> result@[i] == c1@[i],
        c2.len() > c1.len() ==> forall|i: int| 
            c1.len() <= i < c2.len() ==> result@[i] == -c2@[i],
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): added decreases clauses to all loops to fix verification error */
    let len1 = c1.len();
    let len2 = c2.len();
    let maxlen = if len1 >= len2 { len1 } else { len2 };
    let mut result: Vec<i8> = Vec::new();
    let mut i: usize = 0;
    while i < len1 && i < len2
        invariant
            i as int >= 0 && i as int <= maxlen as int,
            result@.len() == i as int,
            forall|k: int| 0 <= k < i as int ==> result@[k] == c1@[k] - c2@[k],
        decreases maxlen - i as int
    {
        let e1 = *c1.get(i).unwrap();
        let e2 = *c2.get(i).unwrap();
        result.push(e1 - e2);
        i = i + 1;
    }
    if len1 > len2 {
        while i < len1
            invariant
                result@.len() == len2 as int + (i as int - len2 as int),
                forall|k: int| 0 <= k < len2 as int ==> result@[k] == c1@[k] - c2@[k],
                forall|k: int| len2 as int <= k < i as int ==> result@[k] == c1@[k],
                i >= len2 && i <= len1,
            decreases len1 - i as int
        {
            result.push(*c1.get(i).unwrap());
            i = i + 1;
        }
    } else if len2 > len1 {
        while i < len2
            invariant
                result@.len() == len1 as int + (i as int - len1 as int),
                forall|k: int| 0 <= k < len1 as int ==> result@[k] == c1@[k] - c2@[k],
                forall|k: int| len1 as int <= k < i as int ==> result@[k] == -c2@[k],
                i >= len1 && i <= len2,
            decreases len2 - i as int
        {
            let e2 = *c2.get(i).unwrap();
            result.push(-e2);
            i = i + 1;
        }
    }
    result
}
// </vc-code>


}
fn main() {}