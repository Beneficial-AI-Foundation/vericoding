// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn tri(n: nat) -> nat
  decreases if n % 2 == 0 { 0 } else { n }
{
  if n == 1 { 3 }
  else if n % 2 == 0 { 1 + n / 2 }
  else { tri((n - 1) as nat) + tri((n - 2) as nat) + tri(n + 1) }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): runtime recursive compute tri using usize, avoiding tri(n+1) recursion */
fn tri_impl(n: usize) -> (res: usize)
    ensures
        res as nat == tri(n as nat),
    decreases
        if n % 2 == 0 { 0 } else { n }
{
    if n == 1 {
        3
    } else if n % 2 == 0 {
        1 + n / 2
    } else {
        let a = tri_impl(n - 1);
        let b = tri_impl(n - 2);
        let c = 1 + (n + 1) / 2;
        a + b + c
    }
}
// </vc-helpers>

// <vc-spec>
fn tribonacci(n: u8) -> (result: Vec<u8>)
  ensures 
    result.len() == n as int + 1 &&
    (forall|i: int| 0 <= i <= n as int ==> result[i] as nat == tri(i as nat))
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): build tribonacci vector using tri_impl, loop uses usize indices and spec invariants relate to tri */
    let mut result: Vec<u8> = Vec::new();
    let mut i: usize = 0;
    while i <= (n as usize)
        invariant
            result.len() == i as int,
            (forall|j: int| 0 <= j && j < i as int ==> result[j] as nat == tri(j as nat)),
        decreases (n as int) - (i as int)
    {
        let t = tri_impl(i);
        result.push(t as u8);
        i = i + 1;
    }
    proof {
        assert(i == (n as usize) + 1);
        assert(result.len() == i as int);
        assert(result.len() == n as int + 1);
        assert(forall|j: int| 0 <= j && j <= n as int ==> result[j] as nat == tri(j as nat));
    }
    result
}
// </vc-code>


}

fn main() {}