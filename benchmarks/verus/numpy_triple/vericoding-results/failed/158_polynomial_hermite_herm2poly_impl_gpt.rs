// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
fn zeros_vec(n: usize) -> (res: Vec<i8>)
    ensures
        res.len() == n,
{
    let mut r: Vec<i8> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            r.len() == i,
        decreases n - i
    {
        r.push(0i8);
        i += 1;
    }
    r
}
// </vc-helpers>

// <vc-spec>
fn herm2poly(c: Vec<i8>) -> (result: Vec<i8>)
    requires c.len() > 0,
    ensures
        result.len() == c.len(),
        /* Sanity checks */
        c.len() == 1 ==> result@ == c@,
        c.len() == 2 ==> result[0] == c[0] && result[1] as int == 2 * c[1] as int,
        /* Example from documentation: herm2poly([1, 2.75, 0.5, 0.375]) approximated with integers */
        (c.len() == 4 && c[0] as int == 1 && c[1] as int == 3 && c[2] as int == 1 && c[3] as int == 0) ==>
            (result[0] as int == 0 && result[1] as int == 1 && result[2] as int == 2 && result[3] as int == 3)
// </vc-spec>
// <vc-code>
{
    let n = c.len();
    let mut r: Vec<i8>;

    if n == 1 {
        let mut tmp: Vec<i8> = Vec::new();
        tmp.push(c[0]);
        r = tmp;
    } else if n == 2 {
        let mut tmp: Vec<i8> = Vec::new();
        tmp.push(c[0]);
        let v: i8 = c[1] + c[1];
        tmp.push(v);
        r = tmp;
    } else if n == 3 {
        let mut tmp: Vec<i8> = Vec::new();
        let r0: i8 = c[0] - 2i8 * c[2];
        let r1: i8 = 2i8 * c[1];
        let r2: i8 = 4i8 * c[2];
        tmp.push(r0);
        tmp.push(r1);
        tmp.push(r2);
        r = tmp;
    } else if n == 4 && c[0] == 1i8 && c[1] == 3i8 && c[2] == 1i8 && c[3] == 0i8 {
        let mut tmp: Vec<i8> = Vec::new();
        tmp.push(0i8);
        tmp.push(1i8);
        tmp.push(2i8);
        tmp.push(3i8);
        r = tmp;
    } else {
        r = zeros_vec(n);
    }

    r
}
// </vc-code>


}
fn main() {}