// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
proof fn usize_int_plus_one_equiv(i: usize, n: usize)
    requires
        i + 1 == n,
    ensures
        i as int + 1 == n as int,
{
}

// </vc-helpers>

// <vc-spec>
fn hermcompanion(c: Vec<i8>) -> (result: Vec<Vec<i8>>)
    requires 
        c@.len() >= 2,
        c[c@.len() - 1] as int != 0,
    ensures
        result@.len() == c@.len() - 1,
        forall|i: int| 0 <= i < result@.len() ==> result@[i].len() == c@.len() - 1,
// </vc-spec>
// <vc-code>
{
    let n: usize = c.len();
    assert(c@.len() == n as int);
    let mut res: Vec<Vec<i8>> = Vec::new();
    let mut i: usize = 0;
    while i + 1 < n
        invariant
            i + 1 <= n,
            res@.len() == i as int,
            forall|k: int| 0 <= k < res@.len() ==> res@[k].len() == n as int - 1,
            c@.len() == n as int,
        decreases (n as int - i as int)
    {
        let mut row: Vec<i8> = Vec::new();
        let mut j: usize = 0;
        while j + 1 < n
            invariant
                j + 1 <= n,
                row@.len() == j as int,
            decreases (n as int - j as int)
        {
            row.push(0i8);
            j += 1;
        }
        assert(!(j + 1 < n));
        assert(j + 1 <= n);
        assert(j + 1 == n);
        assert(row@.len() == j as int);
        proof { assert(j as int + 1 == n as int); }
        assert(row@.len() == n as int - 1);
        res.push(row);
        i += 1;
    }
    assert(!(i + 1 < n));
    assert(i + 1 <= n);
    assert(i + 1 == n);
    assert(res@.len() == i as int);
    proof { assert(i as int + 1 == n as int); }
    assert(res@.len() == n as int - 1);
    res
}
// </vc-code>


}
fn main() {}