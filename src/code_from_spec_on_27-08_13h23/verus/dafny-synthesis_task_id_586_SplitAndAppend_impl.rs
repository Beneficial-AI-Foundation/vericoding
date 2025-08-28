use vstd::prelude::*;

verus! {

// <vc-helpers>
// No updates needed for helpers as the issue is in the code section
// </vc-helpers>

// <vc-spec>
// <vc-spec>
fn split_and_append(l: Seq<int>, n: int) -> (r: Seq<int>)
    requires 
        n >= 0 && n < l.len(),
    ensures 
        r.len() == l.len(),
        forall|i: int| 0 <= i < l.len() ==> r[i] == l[((i + n) as nat % l.len()) as int],
// </vc-spec>
// </vc-spec>

// <vc-code>
fn split_and_append(l: Seq<int>, n: int) -> (r: Seq<int>)
    requires 
        n >= 0 && n < l.len(),
    ensures 
        r.len() == l.len(),
        forall|i: int| 0 <= i < l.len() ==> r[i] == l[((i + n) as nat % l.len()) as int],
{
    let mut result: Vec<int> = Vec::new();
    let l_len = l.len();
    let mut i: usize = 0;

    while i < l_len
        invariant
            l_len == l.len(),
            result.len() == i,
            forall|k: int| 0 <= k < i ==> result[k as usize] == l[((k + n) as nat % l_len) as int],
    {
        let index = ((i as int + n) as nat % l_len) as usize;
        result.push(l[index]);
        i = i + 1;
    }

    result.into_seq()
}
// </vc-code>

fn main() {
}

}