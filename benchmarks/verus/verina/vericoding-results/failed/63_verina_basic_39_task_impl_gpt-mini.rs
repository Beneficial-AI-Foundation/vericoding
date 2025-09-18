// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): modulus subtraction property */
proof fn mod_sub_mod(a: int, b: int, m: int)
    requires
        m > 0,
    ensures
        ((a - b) % m) == ((a - (b % m)) % m),
{
    proof {
        let bb = b % m;
        // b = bb + t*m for some t, so a - b = a - bb - t*m, and modulo m ignores multiples of m
        assert(b == bb + ((b - bb) / m) * m);
        assert((a - b) % m == (a - bb - ((b - bb) / m) * m) % m);
        assert((a - bb - ((b - bb) / m) * m) % m == (a - bb) % m);
    }
}

/* helper modified by LLM (iteration 5): relate usize and int modulo */
proof fn usize_int_mod_equiv(n: usize, m: int)
    requires
        m > 0,
    ensures
        (n as int % m) == ((n % (m as usize)) as int),
{
    proof {
        let mu = m as usize;
        let k = n % mu;
        let q = n / mu;
        let q_i = q as int;
        assert(n as int == k as int + q_i * m);
        assert((n as int) % m == (k as int) % m);
        // 0 <= k < mu and mu == m as usize and m>0, so 0 <= k as int < m
        assert((k as int) % m == k as int);
        assert((n as int) % m == k as int);
    }
}

// </vc-helpers>

// <vc-spec>
fn rotate_right(l: &Vec<i32>, n: usize) -> (result: Vec<i32>)
    ensures
        result.len() == l.len(),
        forall|i: int| 0 <= i < l.len() ==> {
            let len = l.len() as int;
            let rotated_index = ((i - n as int + len) % len) as int;
            #[trigger] result[i] == l[rotated_index]
        },
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): use int-based loop indices and cast modulo results to usize for Vec indexing */
    let len = l.len();
    if len == 0 {
        return Vec::new();
    }
    let k = n % len;
    let len_i = len as int;
    let k_i = k as int;
    let mut res: Vec<i32> = Vec::new();
    let mut i: int = 0;
    while i < len_i
        invariant
            res.len() == i as usize,
            0 <= i,
            i <= len_i,
            forall |j: int| 0 <= j < i ==> res[j as usize] == l[(((j - k_i + len_i) % len_i) as usize)],
        decreases
            len_i - i
    {
        let src = ((i - k_i + len_i) % len_i) as usize;
        res.push(l[src].clone());
        i += 1;
    }
    res
}

// </vc-code>

}
fn main() {}