// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
proof fn lemma_mod_range(x: int, m: int)
    requires
        m > 0,
    ensures
        x % m >= 0,
        x % m < m,
{
    if m > 0 {
        assert(0 <= x % m < m);
    }
}

proof fn lemma_mod_rotation_odd(i: int, n: int)
    requires
        n > 0,
    ensures
        ((i + n/2) % n) == ((i + n - (n + 1)/2) % n),
{
    assert(n % 2 != 0 ==> n/2 == (n - 1)/2);
    assert(n % 2 != 0 ==> (n + 1)/2 == (n + 1)/2);
    assert((i + n/2) % n == (i + n - (n + 1)/2) % n);
}

proof fn lemma_mod_rotation(i: int, n: int)
    requires
        n > 0,
    ensures
        (if n % 2 == 0 {
            (i + n - n/2) % n == (i + n/2) % n
        } else {
            true
        }),
{
    if n % 2 == 0 {
        let half = n/2;
        assert(n - half == half);
    }
}
// </vc-helpers>

// <vc-spec>
fn fftshift(x: Vec<f32>) -> (result: Vec<f32>)
    ensures
        result.len() == x.len(),
        forall|i: int| 0 <= i < result.len() as int ==> 
            result[i as int] == x[((i + (x.len() as int) - (x.len() as int) / 2) % (x.len() as int)) as int]
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Fixed int/nat usage in executable code */
{
    let n: usize = x.len();
    if n == 0 {
        return Vec::empty();
    }
    let half_int = x.len() / 2;
    let n_int = x.len();
    let half_int_val: usize = half_int;
    let mut result = Vec::with_capacity(n);
    let mut i: usize = 0;
    while i < n
        invariant
            result@.len() == i,
            forall|j: nat| j < i ==> 
                result@[j] == x@[(((j as int) + n_int as int - half_int_val as int) % n_int as int) as nat],
        decreases n - i,
    {
        let idx: usize = (i + n_int - half_int_val) % n_int;
        result.push(x[idx]);
        i = i + 1;
    }
    result
}
// </vc-code>


}
fn main() {}