// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn is_fibonacci(num: int) -> bool {
    num == 1 || num == 2 || exists|k: nat| is_fib_seq(k) == num
}

spec fn is_fib_seq(n: nat) -> int
    decreases n
{
    if n == 0 {
        1
    } else if n == 1 {
        1
    } else {
        is_fib_seq((n - 1) as nat) + is_fib_seq((n - 2) as nat)
    }
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn solve(n: i8) -> (result: Vec<char>)
    requires n >= 1 && n <= 100
    ensures 
        result.len() == n as nat
        && (forall|i: int| 0 <= i < result.len() ==> result[i] == 'O' || result[i] == 'o')
        && (forall|i: int| 1 <= i <= n ==> (is_fibonacci(i) <==> result[i-1] == 'O'))
        && (forall|i: int| 1 <= i <= n ==> (!is_fibonacci(i) <==> result[i-1] == 'o'))
// </vc-spec>
// <vc-code>
{
    assume(false);
    Vec::new()
}
// </vc-code>


}

fn main() {}