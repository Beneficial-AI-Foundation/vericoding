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
/* helper modified by LLM (iteration 2): fixed compilation errors by declaring ghost variables */
fn find_love_triangle(n: i8, f: &Vec<i8>) -> (result: bool)
    requires
        valid_input(n as int, f@.map(|i: int, x: i8| x as int)),
    ensures
        result == has_love_triangle(n as int, f@.map(|i: int, x: i8| x as int)),
{
    let ghost n_int = n as int;
    let ghost f_seq = f@.map(|_i: int, x: i8| x as int);
    let a = zero_indexed_array(n_int, f_seq);

    let mut i: i8 = 0;
    while i < n
        invariant
            0 <= i <= n,
            valid_input(n_int, f_seq),
            f@.map(|_i: int, x: i8| x as int) == f_seq,
            a == zero_indexed_array(n_int, f_seq),
            forall|k: int| 0 <= k < (i as int) ==> a[a[a[k]]] != k,
        decreases n - i
    {
        let i_usize = i as usize;
        let lover1_val = f[i_usize];
        let lover1_idx = (lover1_val - 1) as usize;
        let lover2_val = f[lover1_idx];
        let lover2_idx = (lover2_val - 1) as usize;
        let lover3_val = f[lover2_idx];

        if lover3_val == i + 1 {
            proof {
                let i_int = i as int;
                assert(a[a[a[i_int]]] == i_int);
                assert(has_love_triangle_with(n_int, a));
            }
            return true;
        }
        i = i + 1;
    }
    
    proof {
        assert(!has_love_triangle_with(n_int, a));
    }
    return false;
}
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
    /* code modified by LLM (iteration 2): no changes, as errors were in helper function */
    let has_triangle = find_love_triangle(n, &f);
    if has_triangle {
        return String::new("YES");
    } else {
        return String::new("NO");
    }
}
// </vc-code>


}

fn main() {}