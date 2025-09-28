// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): change prefix length parameter to int and adapt split lemma to use int with casts to nat for skips */
spec fn correlation_sum_prefix(a: Seq<i32>, v: Seq<i32>, k: int, i: int) -> int
    requires
        0 <= i,
    decreases
        i
{
    if i == 0 {
        0
    } else {
        a[k] * v[0] + correlation_sum_prefix(a, v.skip(1), k + 1, i - 1)
    }
}

fn correlation_sum_split(a: Seq<i32>, v: Seq<i32>, k: int, i: int)
    requires
        0 <= i,
        (i as nat) <= v.len(),
    ensures
        correlation_sum(a, v, k) == correlation_sum_prefix(a, v, k, i) + correlation_sum(a, v.skip(i as nat), k + i),
    decreases
        i,
{
    proof {
        if i == 0 {
            assert(correlation_sum(a, v, k) == correlation_sum_prefix(a, v, k, 0) + correlation_sum(a, v.skip(0), k + 0));
        } else {
            assert(v.len() > 0);
            assert(correlation_sum(a, v, k) == a[k] * v[0] + correlation_sum(a, v.skip(1), k + 1));
            assert(correlation_sum_prefix(a, v, k, i) == a[k] * v[0] + correlation_sum_prefix(a, v.skip(1), k + 1, i - 1));
            correlation_sum_split(a, v.skip(1), k + 1, i - 1);
            assert(correlation_sum(a, v.skip(1), k + 1) == correlation_sum_prefix(a, v.skip(1), k + 1, i - 1) + correlation_sum(a, v.skip(i as nat), k + (i - 1) + 1));
            assert(k + (i - 1) + 1 == k + i);
            assert(correlation_sum(a, v.skip(1), k + 1) == correlation_sum_prefix(a, v.skip(1), k + 1, i - 1) + correlation_sum(a, v.skip(i as nat), k + i));
            assert(a[k] * v[0] + correlation_sum(a, v.skip(1), k + 1) == a[k] * v[0] + correlation_sum_prefix(a, v.skip(1), k + 1, i - 1) + correlation_sum(a, v.skip(i as nat), k + i));
            assert(correlation_sum(a, v, k) == correlation_sum_prefix(a, v, k, i) + correlation_sum(a, v.skip(i as nat), k + i));
        }
    }
}

// </vc-helpers>

// <vc-spec>
spec fn correlation_sum(a: Seq<i32>, v: Seq<i32>, k: int) -> int
    decreases v.len()
{
    if v.len() == 0 {
        0
    } else {
        a[k] * v[0] + correlation_sum(a, v.skip(1), k + 1)
    }
}

fn correlate(a: Vec<i32>, v: Vec<i32>) -> (result: Vec<i32>)
    requires 
        v.len() > 0,
        v.len() <= a.len(),
    ensures
        result.len() == a.len() + 1 - v.len(),
        forall|k: int| 0 <= k < result.len() ==> 
            result[k] == correlation_sum(a@, v@, k),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): compute sliding correlation using prefix-spec and proper casts */
    let mut result: Vec<i32> = Vec::new();
    let m: usize = a.len() + 1 - v.len();
    let mut k: usize = 0;
    while k < m
        invariant
            k <= m,
            result.len() == k,
            forall|j: int| 0 <= j < (k as int) ==> result[j as usize] as int == correlation_sum(a@, v@, j),
        decreases m - k
    {
        let mut sum: i64 = 0;
        let mut i: usize = 0;
        let n: usize = v.len();
        while i < n
            invariant
                i <= n,
                sum as int == correlation_sum_prefix(a@, v@, k as int, i as int),
            decreases n - i
        {
            sum = sum + (a[k + i] as i64) * (v[i] as i64);
            i += 1;
        }
        result.push(sum as i32);
        k += 1;
    }
    result
}

// </vc-code>


}
fn main() {}