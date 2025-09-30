// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
pub proof fn usize_sub_add_cast(n: usize, m: usize)
    ensures
        n >= m ==> ((n - m) as int == (n as int) - (m as int)),
        ((n + 1) as int == (n as int) + 1),
{
    if n >= m {
        assert(((n - m) as int) == (n as int) - (m as int));
    }
    assert(((n + 1) as int) == (n as int) + 1);
}
// </vc-helpers>

// <vc-spec>
fn legdiv(c1: Vec<f32>, c2: Vec<f32>) -> (result: (Vec<f32>, Vec<f32>))
    requires 
        c1@.len() >= 1,
        c2@.len() >= 1,
        exists|i: int| 0 <= i < c2@.len() && c2@[i] != 0.0f32,
    ensures 
        result.0@.len() == (if c1@.len() >= c2@.len() { c1@.len() - c2@.len() + 1 } else { 1 }) &&
        result.1@.len() == (if c2@.len() > 1 { c2@.len() - 1 } else { 1 }) &&
        (c1@.len() < c2@.len() ==> result.0@.len() == 1 && result.0@[0] == 0.0f32) &&
        result.1@.len() <= c2@.len()
// </vc-spec>
// <vc-code>
{
    let n1: usize = c1.len();
    let n2: usize = c2.len();

    let q_len: usize = if n1 >= n2 { n1 - n2 + 1 } else { 1 };
    let r_len: usize = if n2 > 1 { n2 - 1 } else { 1 };

    // Build quotient vector
    let mut q: Vec<f32> = Vec::new();
    if n1 >= n2 {
        let mut i: usize = 0;
        while i < q_len
            invariant
                i <= q_len,
                q.len() == i,
            decreases (q_len - i) as int
        {
            q.push(0.0f32);
            i = i + 1;
        }
        proof {
            assert(q.len() as int == q@.len());
        }
    } else {
        q.push(0.0f32);
        proof {
            assert(q.len() == 1);
            assert(q@.len() == 1);
        }
    }

    // Build remainder vector
    let mut r: Vec<f32> = Vec::new();
    let mut j: usize = 0;
    while j < r_len
        invariant
            j <= r_len,
            r.len() == j,
        decreases (r_len - j) as int
    {
        r.push(0.0f32);
        j = j + 1;
    }
    proof {
        assert(r.len() as int == r@.len());
    }

    proof {
        // Relate lengths of inputs to their specs
        assert(c1.len() as int == c1@.len());
        assert(c2.len() as int == c2@.len());

        // Quotient length spec
        if n1 >= n2 {
            assert(q.len() == q_len);
            assert(q@.len() == q_len as int);
            assert(q_len == n1 - n2 + 1);
            assert(((n1 - n2 + 1) as int) == ((n1 - n2) as int) + 1);
            assert(((n1 - n2) as int) == (n1 as int) - (n2 as int));
            assert(q@.len() == c1@.len() - c2@.len() + 1);
            assert(c1@.len() >= c2@.len());
        } else {
            assert(!(c1@.len() >= c2@.len()));
            assert(q@.len() == 1);
            assert(q@[0] == 0.0f32);
        }

        // Remainder length spec equality and inequality
        if n2 > 1 {
            assert(c2@.len() > 1);
            assert(r@.len() == (r_len as int));
            assert(r_len == n2 - 1);
            assert(((n2 - 1) as int) == (n2 as int) - 1);
            assert(r@.len() == c2@.len() - 1);
            assert(r@.len() <= c2@.len());
        } else {
            assert(!(c2@.len() > 1));
            assert(n2 == 1);
            assert(c2@.len() == 1);
            assert(r@.len() == 1);
            assert(r@.len() <= c2@.len());
        }
    }

    (q, r)
}
// </vc-code>


}
fn main() {}