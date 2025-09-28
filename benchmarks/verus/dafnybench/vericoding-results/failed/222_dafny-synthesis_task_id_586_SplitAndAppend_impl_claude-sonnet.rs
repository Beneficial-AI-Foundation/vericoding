use vstd::prelude::*;

verus! {

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn split_and_append(l: Seq<int>, n: int) -> (r: Seq<int>)
    requires 
        n >= 0 && n < l.len(),
    ensures 
        r.len() == l.len(),
        forall|i: int| 0 <= i < l.len() ==> r[i] == l[((i + n) as nat % l.len()) as int],
// </vc-spec>
// <vc-code>
{
    let len = l.len();
    let mut result = Seq::<int>::empty();
    let mut i = 0;
    
    while i < len
        invariant
            i <= len,
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result[j] == l[((j + n) % len) as int],
    {
        proof {
            let idx_calc = (i + n) % len;
            assert(0 <= idx_calc < len);
        }
        let idx = ((i + n) % len) as usize;
        result = result.push(l[idx]);
        i = i + 1;
    }
    
    result
}
// </vc-code>

fn main() {
}

}