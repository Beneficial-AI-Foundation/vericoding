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
proof fn fib_monotonic(i: nat, j: nat)
    requires i <= j
    ensures is_fib_seq(i) <= is_fib_seq(j)
    decreases j - i
{
    if i < j {
        fib_monotonic(i, (j - 1) as nat);
        assert(is_fib_seq(i) <= is_fib_seq((j - 1) as nat));
        assert(is_fib_seq((j - 1) as nat) <= is_fib_seq(j));
    }
}

spec fn fib_up_to(n: nat) -> Seq<int> 
    decreases n
{
    if n == 0 {
        Seq::empty()
    } else {
        fib_up_to((n - 1) as nat).push(is_fib_seq((n - 1) as nat))
    }
}

proof fn fib_exists_up_to(num: int, n: nat)
    requires 1 <= num <= is_fib_seq(n)
    ensures exists|k: nat| k <= n && is_fib_seq(k) == num
    decreases n
{
    if n == 0 {
        assert(is_fib_seq(0) == 1);
    } else {
        if num == is_fib_seq(n) {
            // Found it
        } else {
            fib_exists_up_to(num, (n - 1) as nat);
        }
    }
}

fn find_fib_upper_bound(num: int) -> (bound: nat)
    requires num >= 1
    ensures bound >= 0 && is_fib_seq(bound) >= num
{
    /* helper modified by LLM (iteration 3): Fix nat/int type issues */
    let mut i: u64 = 0;
    while is_fib_seq(i as nat) < num
        invariant
            i >= 0,
            is_fib_seq(i as nat) < num
        decreases num - is_fib_seq(i as nat)
    {
        i = i + 1;
        fib_monotonic((i - 1) as nat, i as nat);
    }
    i as nat
}
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
    /* code modified by LLM (iteration 3): Fix nat/int type issue in while condition */
    let mut result = Vec::with_capacity(n as usize);
    let mut i: i8 = 1;
    
    while i <= n
        invariant
            result@.len() == (i - 1) as nat,
            forall|j: int| 0 <= j < result@.len() ==> result@[j] == 'O' || result@[j] == 'o',
            forall|j: int| 1 <= j < i as int ==> (is_fibonacci(j) <==> result@[(j - 1) as nat] == 'O'),
            forall|j: int| 1 <= j < i as int ==> (!is_fibonacci(j) <==> result@[(j - 1) as nat] == 'o')
    {
        let bound = find_fib_upper_bound(i as int);
        let is_fib = is_fib_seq(bound) == (i as int);
        
        if is_fib {
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