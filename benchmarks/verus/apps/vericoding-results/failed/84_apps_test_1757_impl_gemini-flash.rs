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
/* code modified by LLM (iteration 5): Fixed type casting of `i` in `is_fibonacci(i as int)` to avoid compilation error. */
{
    let mut result: Vec<char> = Vec::new();
    let mut i: i8 = 1;
    while i <= n
        invariant
            result.len() == (i - 1) as nat,
            forall|j: int| 0 <= j < i - 1 ==> (is_fibonacci(j + 1) <==> result[j] == 'O'),
            forall|j: int| 0 <= j < i - 1 ==> (!is_fibonacci(j + 1) <==> result[j] == 'o'),
            i <= n + 1,
            n >= 1,
    decreases (n - i) as int
    {
        proof {
            assert(i as int >= 0);
        }
        if is_fibonacci(i as int) {
            result.push('O');
        } else {
            result.push('o');
        }
        i = i + 1;
    }
    result
}
// </vc-code>


}

fn main() {}