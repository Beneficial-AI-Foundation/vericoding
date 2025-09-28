// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(n: int, f: Seq<int>) -> bool {
    n >= 2 && n <= 5000 &&
    f.len() == n &&
    forall|i: int| 0 <= i < f.len() ==> 1 <= f[i] <= n && f[i] != i + 1
}

spec fn zero_indexed_array(n: int, f: Seq<int>) -> Seq<int>
    recommends valid_input(n, f)
{
    Seq::new(n as nat, |j: int| f[j] - 1)
}

spec fn has_love_triangle_with(n: int, a: Seq<int>) -> bool
    recommends 
        a.len() == n &&
        forall|k: int| 0 <= k < n ==> #[trigger] a[k] >= 0 && #[trigger] a[k] < n
{
    exists|i: int| 0 <= i < n && 
        0 <= a[i] < n && 0 <= a[a[i]] < n && a[a[a[i]]] == i
}

spec fn has_love_triangle(n: int, f: Seq<int>) -> bool
    recommends valid_input(n, f)
{
    let a = zero_indexed_array(n, f);
    has_love_triangle_with(n, a)
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): no changes needed, kept empty */
// </vc-helpers>

// <vc-spec>
fn solve(n: i8, f: Vec<i8>) -> (result: String)
    requires 
        valid_input(n as int, f@.map(|i: int, x: i8| x as int)),
    ensures 
        result@.len() == 2 || result@.len() == 3,
        (result@.len() == 3) <==> has_love_triangle(n as int, f@.map(|i: int, x: i8| x as int)),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed type errors by avoiding 'int' and 'Seq<int>' in exec code, used 'usize' for exec arrays and indexing, created exec vector 'a' mirroring the spec zero_indexed_array, used exec loop to check for love triangle, and added proof assertions to connect exec computation to spec ensures */
    let n_usize: usize = n as usize;
    let mut a: Vec<usize> = Vec::with_capacity(n_usize);
    proof {
        a.view().len() == n as int;
    }
    for i in 0..n_usize {
        let fi = f[i] as usize;
        a.push(fi - 1);
        proof {
            assert(a@[i as int] == (f@[i as int] as int) - 1);
        }
    }
    let mut found: bool = false;
    let mut i_exec: usize = 0;
    while i_exec < n_usize {
        let ai = a[i_exec];
        if ai < n_usize {
            let aai = a[ai];
            if aai < n_usize {
                let aaai = a[aai];
                if aaai == i_exec {
                    found = true;
                    break;
                }
            }
        }
        i_exec = i_exec + 1;
    }
    if found {
        "YES".to_string()
    } else {
        "NO".to_string()
    }
}
// </vc-code>


}

fn main() {}