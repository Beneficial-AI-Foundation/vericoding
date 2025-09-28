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
/* helper modified by LLM (iteration 5): Removed `result` from ensrures clause which caused compilation error */
proof fn get_value_from_seq(s: Seq<int>, i: int) -> int
    requires 0 <= i < s.len()
{
    s[i]
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
/* code modified by LLM (iteration 5): Fixed compilation error by adding missing comma in the if condition. */
{
    // Create a ghost sequence `a` for verification
    let ghost a = zero_indexed_array(n as int, f@.map(|i: int, x: i8| x as int));

    let mut i: i32 = 0;
    while i < n as i32
        invariant
            0 <= i <= n as i32,
            // loop invariant: no love triangle found up to `i` (ghost property)
            forall|j: int| 0 <= j < i ==> !(0 <= a[j] < n as int && 0 <= a[a[j]] < n as int && a[a[a[j]]] == j),
        decreases (n as i32) - i
    {
        // These assertions are to help Verus prove the loop invariant and postconditions
        proof {
            let f_int_seq = f@.map(|k: int, x: i8| x as int);
            valid_input(n as int, f_int_seq);

            assert(a.len() == n as int);
            assert(forall|k: int| 0 <= k < n as int ==> #[trigger] a[k] >= 0 && #[trigger] a[k] < n as int);
        }

        // Check for love triangle (ghost condition used only in proof context)
        // The `if` condition itself needs to operate on concrete types for runtime execution
        // This part needs to be understood as a *ghost* check that might influence the return
        // but the values used *inside* the check are from `a`, which is `ghost`.
        if (0 <= i as int && i as int < n as int && // Ensure i is within bounds for ghost access
            0 <= a[i as int] && a[i as int] < n as int &&
            0 <= a[a[i as int]] && a[a[i as int]] < n as int &&
            a[a[a[i as int]]] == i as int)
        {
            proof {
                assert(has_love_triangle_with(n as int, a));
                assert(has_love_triangle(n as int, f@.map(|k: int, x: i8| x as int)));
            }
            return format!("YES");
        }
        i = i + 1;
    }

    proof {
        assert(!has_love_triangle(n as int, f@.map(|k: int, x: i8| x as int)));
    }
    format!("NO")
}
// </vc-code>


}

fn main() {}