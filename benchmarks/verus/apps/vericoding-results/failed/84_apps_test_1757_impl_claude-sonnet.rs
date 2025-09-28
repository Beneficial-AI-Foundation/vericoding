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
/* helper modified by LLM (iteration 5): fixed lemma to properly prove both directions */
proof fn lemma_fib_seq_values(k: nat)
    ensures
        k == 0 ==> is_fib_seq(k) == 1,
        k == 1 ==> is_fib_seq(k) == 1,
        k == 2 ==> is_fib_seq(k) == 2,
        k == 3 ==> is_fib_seq(k) == 3,
        k == 4 ==> is_fib_seq(k) == 5,
        k == 5 ==> is_fib_seq(k) == 8,
        k == 6 ==> is_fib_seq(k) == 13,
        k == 7 ==> is_fib_seq(k) == 21,
        k == 8 ==> is_fib_seq(k) == 34,
        k == 9 ==> is_fib_seq(k) == 55,
        k == 10 ==> is_fib_seq(k) == 89
    decreases k
{
    if k <= 1 {
    } else {
        lemma_fib_seq_values((k - 1) as nat);
        lemma_fib_seq_values((k - 2) as nat);
    }
}

proof fn lemma_fibonacci_characterization(i: int)
    ensures
        is_fibonacci(i) <==> (i == 1 || i == 2 || i == 3 || i == 5 || i == 8 || i == 13 || i == 21 || i == 34 || i == 55 || i == 89)
{
    lemma_fib_seq_values(0);
    lemma_fib_seq_values(1);
    lemma_fib_seq_values(2);
    lemma_fib_seq_values(3);
    lemma_fib_seq_values(4);
    lemma_fib_seq_values(5);
    lemma_fib_seq_values(6);
    lemma_fib_seq_values(7);
    lemma_fib_seq_values(8);
    lemma_fib_seq_values(9);
    lemma_fib_seq_values(10);
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
    /* code modified by LLM (iteration 5): use i8 instead of nat for executable code */
    let mut result = Vec::new();
    let mut i: i8 = 1;
    
    while i <= n
        invariant
            1 <= i <= n + 1,
            result.len() == (i - 1) as nat,
            forall|j: int| 0 <= j < result.len() ==> result[j] == 'O' || result[j] == 'o',
            forall|j: int| 1 <= j < i ==> (is_fibonacci(j) <==> result[j-1] == 'O'),
            forall|j: int| 1 <= j < i ==> (!is_fibonacci(j) <==> result[j-1] == 'o')
        decreases n - i
    {
        proof {
            lemma_fibonacci_characterization(i as int);
        }
        
        if i == 1 || i == 2 || i == 3 || i == 5 || i == 8 || i == 13 || i == 21 || i == 34 || i == 55 || i == 89 {
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