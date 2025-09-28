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
/* helper modified by LLM (iteration 5): fixed lemma syntax by adding proof blocks */
proof fn array_bounds_preserved(n: int, f: Seq<int>)
    requires valid_input(n, f)
    ensures
        forall|k: int| 0 <= k < n ==> #[trigger] zero_indexed_array(n, f)[k] >= 0 && #[trigger] zero_indexed_array(n, f)[k] < n
{
}

proof fn triangle_detection_lemma(n: int, a: Seq<int>, i: int)
    requires
        a.len() == n,
        forall|k: int| 0 <= k < n ==> #[trigger] a[k] >= 0 && #[trigger] a[k] < n,
        0 <= i < n,
        0 <= a[i] < n,
        0 <= a[a[i]] < n,
        a[a[a[i]]] == i
    ensures has_love_triangle_with(n, a)
{
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
    /* code modified by LLM (iteration 5): added decreases clause to while loop */
    let mut i = 0;
    
    proof {
        let a_spec = zero_indexed_array(n as int, f@.map(|i: int, x: i8| x as int));
        array_bounds_preserved(n as int, f@.map(|i: int, x: i8| x as int));
    }
    
    while i < n
        invariant
            0 <= i <= n,
            forall|k: int| 0 <= k < i ==> {
                let ai = f@[k] as int - 1;
                let aai = f@[ai] as int - 1;
                let aaai = f@[aai] as int - 1;
                aaai != k
            },
        decreases n - i
    {
        let ai = f[i as usize] - 1;
        let aai = f[ai as usize] - 1;
        let aaai = f[aai as usize] - 1;
        
        if aaai == i {
            proof {
                let a_spec = zero_indexed_array(n as int, f@.map(|i: int, x: i8| x as int));
                triangle_detection_lemma(n as int, a_spec, i as int);
            }
            return "YES".to_string();
        }
        
        i = i + 1;
    }
    
    "NO".to_string()
}
// </vc-code>


}

fn main() {}