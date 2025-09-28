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

spec fn triangle_check(a: &Vec<int>, n: int, i: int) -> bool
    requires
        0 <= i < n,
        a.len() == n,
    ensures
        result == (0 <= a[i] < n && 0 <= a[a[i]] < n && a[a[a[i]]] == i)
{
    0 <= a[i] < n && 0 <= a[a[i]] < n && a[a[a[i]]] == i
}

spec fn ghost_idx(a: Seq<int>, i: int) -> int
    requires 0 <= i < a.len()
{
    a[i]
}

proof fn transitive_check(a: Seq<int>, n: int, i: int)
    requires
        n == a.len(),
        0 <= i < n,
        0 <= a[i] < n,
        0 <= a[a[i]] < n,
        a[a[a[i]]] == i
    ensures
        has_love_triangle_with(n, a)
{
    assert(0 <= a[i] < n);
    assert(0 <= a[a[i]] < n);
    assert(ghost_idx(a, ghost_idx(a, ghost_idx(a, i))) == i);
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
    let mut i: usize = 0;
    let size = n as usize;
    let mut zero_f: Vec<i8> = Vec::with_capacity(size);
    
    while i < size
        invariant
            i <= size,
            zero_f@.len() == i,
            forall|j: int| 0 <= j < i ==> zero_f@[j] == (f@[j] - 1) as i8,
    {
        zero_f.push(f[i] - 1);
        i = i + 1;
    }
    
    let mut x: usize = 0;
    while x < size
        invariant
            x <= size,
    {
        let a = zero_f[x] as usize;
        if a < size {
            let b = zero_f[a] as usize;
            if b < size {
                let c = zero_f[b] as usize;
                if c == x {
                    let proof_result = String::from("yes");
                    return proof_result;
                }
            }
        }
        x = x + 1;
    }
    
    let no_result = String::from("no");
    no_result
}
// </vc-code>


}

fn main() {}