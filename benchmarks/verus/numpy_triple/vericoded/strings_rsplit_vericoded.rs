// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
proof fn lemma_u8_nonneg(x: u8)
    ensures
        0 <= x as int,
        1 <= x as int + 1,
{
}

fn make_singleton(s: String) -> (v: Vec<String>)
    ensures
        v.len() == 1,
        v[0]@ == s@,
{
    let mut v: Vec<String> = Vec::new();
    v.push(s);
    v
}
// </vc-helpers>

// <vc-spec>
fn rsplit(a: Vec<String>, sep: String, maxsplit: u8) -> (result: Vec<Vec<String>>)
    requires 
        sep@.len() > 0,
    ensures
        result.len() == a.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i].len() > 0,
        maxsplit as int == 0 ==> forall|i: int| 0 <= i < result.len() ==> 
            result[i].len() == 1 && result[i][0]@ == a[i]@,
        forall|i: int| 0 <= i < result.len() ==> result[i].len() <= maxsplit as int + 1,
        forall|i: int| 0 <= i < result.len() ==> 
            (a[i]@.len() == 0 ==> result[i].len() == 1 && result[i][0]@.len() == 0),
// </vc-spec>
// <vc-code>
{
    let mut r: Vec<Vec<String>> = Vec::new();
    let mut i: usize = 0;
    while i < a.len()
        invariant
            i as int <= a.len(),
            r.len() == i as int,
            forall|j: int| 0 <= j < r.len() ==> r[j].len() == 1 && r[j][0]@ == a[j]@,
            forall|j: int| 0 <= j < r.len() ==> r[j].len() > 0,
            forall|j: int| 0 <= j < r.len() ==> r[j].len() <= maxsplit as int + 1,
        decreases a.len() - i as int
    {
        proof { lemma_u8_nonneg(maxsplit); }
        let s = a[i].clone();
        let v = make_singleton(s);
        r.push(v);
        i = i + 1;
    }
    r
}
// </vc-code>


}
fn main() {}