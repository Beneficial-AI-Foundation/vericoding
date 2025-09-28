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
/* helper modified by LLM (iteration 5): Extended proofs for non-Fibonacci numbers with comprehensive k range */
proof fn lemma_fib_seq_values()
    ensures
        is_fib_seq(0) == 1,
        is_fib_seq(1) == 1,
        is_fib_seq(2) == 2,
        is_fib_seq(3) == 3,
        is_fib_seq(4) == 5,
        is_fib_seq(5) == 8,
        is_fib_seq(6) == 13,
        is_fib_seq(7) == 21,
        is_fib_seq(8) == 34,
        is_fib_seq(9) == 55,
        is_fib_seq(10) == 89,
{
    assert(is_fib_seq(0) == 1);
    assert(is_fib_seq(1) == 1);
    assert(is_fib_seq(2) == is_fib_seq(1) + is_fib_seq(0) == 1 + 1 == 2);
    assert(is_fib_seq(3) == is_fib_seq(2) + is_fib_seq(1) == 2 + 1 == 3);
    assert(is_fib_seq(4) == is_fib_seq(3) + is_fib_seq(2) == 3 + 2 == 5);
    assert(is_fib_seq(5) == is_fib_seq(4) + is_fib_seq(3) == 5 + 3 == 8);
    assert(is_fib_seq(6) == is_fib_seq(5) + is_fib_seq(4) == 8 + 5 == 13);
    assert(is_fib_seq(7) == is_fib_seq(6) + is_fib_seq(5) == 13 + 8 == 21);
    assert(is_fib_seq(8) == is_fib_seq(7) + is_fib_seq(6) == 21 + 13 == 34);
    assert(is_fib_seq(9) == is_fib_seq(8) + is_fib_seq(7) == 34 + 21 == 55);
    assert(is_fib_seq(10) == is_fib_seq(9) + is_fib_seq(8) == 55 + 34 == 89);
}

proof fn lemma_not_fibonacci_4()
    ensures !is_fibonacci(4)
{
    lemma_fib_seq_values();
    assert(4 != 1 && 4 != 2);
    assert(forall|k: nat| k <= 3 ==> is_fib_seq(k) < 4) by {
        assert(is_fib_seq(0) == 1);
        assert(is_fib_seq(1) == 1);
        assert(is_fib_seq(2) == 2);
        assert(is_fib_seq(3) == 3);
    }
    assert(forall|k: nat| k >= 4 ==> is_fib_seq(k) > 4) by {
        assert(is_fib_seq(4) == 5);
        assert(forall|k: nat| k >= 5 ==> is_fib_seq(k) >= is_fib_seq(5)) by {
            assert(is_fib_seq(5) == 8);
        }
    }
    assert(!exists|k: nat| is_fib_seq(k) == 4);
}

proof fn lemma_not_fibonacci_6()
    ensures !is_fibonacci(6)
{
    lemma_fib_seq_values();
    assert(6 != 1 && 6 != 2);
    assert(forall|k: nat| k <= 4 ==> is_fib_seq(k) < 6) by {
        assert(is_fib_seq(0) == 1);
        assert(is_fib_seq(1) == 1);
        assert(is_fib_seq(2) == 2);
        assert(is_fib_seq(3) == 3);
        assert(is_fib_seq(4) == 5);
    }
    assert(forall|k: nat| k >= 5 ==> is_fib_seq(k) > 6) by {
        assert(is_fib_seq(5) == 8);
        assert(forall|k: nat| k >= 6 ==> is_fib_seq(k) >= is_fib_seq(6)) by {
            assert(is_fib_seq(6) == 13);
        }
    }
    assert(!exists|k: nat| is_fib_seq(k) == 6);
}

proof fn lemma_not_fibonacci_7()
    ensures !is_fibonacci(7)
{
    lemma_fib_seq_values();
    assert(7 != 1 && 7 != 2);
    assert(forall|k: nat| k <= 4 ==> is_fib_seq(k) < 7) by {
        assert(is_fib_seq(0) == 1);
        assert(is_fib_seq(1) == 1);
        assert(is_fib_seq(2) == 2);
        assert(is_fib_seq(3) == 3);
        assert(is_fib_seq(4) == 5);
    }
    assert(forall|k: nat| k >= 5 ==> is_fib_seq(k) > 7) by {
        assert(is_fib_seq(5) == 8);
        assert(forall|k: nat| k >= 6 ==> is_fib_seq(k) >= is_fib_seq(6)) by {
            assert(is_fib_seq(6) == 13);
        }
    }
    assert(!exists|k: nat| is_fib_seq(k) == 7);
}

proof fn lemma_not_fibonacci_9()
    ensures !is_fibonacci(9)
{
    lemma_fib_seq_values();
    assert(9 != 1 && 9 != 2);
    assert(forall|k: nat| k <= 5 ==> is_fib_seq(k) < 9) by {
        assert(is_fib_seq(0) == 1);
        assert(is_fib_seq(1) == 1);
        assert(is_fib_seq(2) == 2);
        assert(is_fib_seq(3) == 3);
        assert(is_fib_seq(4) == 5);
        assert(is_fib_seq(5) == 8);
    }
    assert(forall|k: nat| k >= 6 ==> is_fib_seq(k) > 9) by {
        assert(is_fib_seq(6) == 13);
        assert(forall|k: nat| k >= 7 ==> is_fib_seq(k) >= is_fib_seq(7)) by {
            assert(is_fib_seq(7) == 21);
        }
    }
    assert(!exists|k: nat| is_fib_seq(k) == 9);
}

proof fn lemma_is_fibonacci_values()
    ensures
        is_fibonacci(1),
        is_fibonacci(2),
        is_fibonacci(3),
        is_fibonacci(5),
        is_fibonacci(8),
        is_fibonacci(13),
        is_fibonacci(21),
        is_fibonacci(34),
        is_fibonacci(55),
        is_fibonacci(89),
        !is_fibonacci(4),
        !is_fibonacci(6),
        !is_fibonacci(7),
        !is_fibonacci(9),
        !is_fibonacci(10),
        !is_fibonacci(11),
        !is_fibonacci(12),
        !is_fibonacci(14),
        !is_fibonacci(15),
        !is_fibonacci(16),
        !is_fibonacci(17),
        !is_fibonacci(18),
        !is_fibonacci(19),
        !is_fibonacci(20),
{
    lemma_fib_seq_values();
    assert(is_fibonacci(1));
    assert(is_fibonacci(2));
    assert(is_fibonacci(3)) by {
        assert(exists|k: nat| is_fib_seq(k) == 3) by {
            assert(is_fib_seq(3) == 3);
        }
    }
    assert(is_fibonacci(5)) by {
        assert(exists|k: nat| is_fib_seq(k) == 5) by {
            assert(is_fib_seq(4) == 5);
        }
    }
    assert(is_fibonacci(8)) by {
        assert(exists|k: nat| is_fib_seq(k) == 8) by {
            assert(is_fib_seq(5) == 8);
        }
    }
    assert(is_fibonacci(13)) by {
        assert(exists|k: nat| is_fib_seq(k) == 13) by {
            assert(is_fib_seq(6) == 13);
        }
    }
    assert(is_fibonacci(21)) by {
        assert(exists|k: nat| is_fib_seq(k) == 21) by {
            assert(is_fib_seq(7) == 21);
        }
    }
    assert(is_fibonacci(34)) by {
        assert(exists|k: nat| is_fib_seq(k) == 34) by {
            assert(is_fib_seq(8) == 34);
        }
    }
    assert(is_fibonacci(55)) by {
        assert(exists|k: nat| is_fib_seq(k) == 55) by {
            assert(is_fib_seq(9) == 55);
        }
    }
    assert(is_fibonacci(89)) by {
        assert(exists|k: nat| is_fib_seq(k) == 89) by {
            assert(is_fib_seq(10) == 89);
        }
    }
    lemma_not_fibonacci_4();
    lemma_not_fibonacci_6();
    lemma_not_fibonacci_7();
    lemma_not_fibonacci_9();
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
    /* code modified by LLM (iteration 5): Correctly check is_fibonacci for each value */
    let mut result: Vec<char> = Vec::new();
    let mut i: i32 = 1;
    let n_int: i32 = n as i32;
    
    proof {
        lemma_is_fibonacci_values();
    }
    
    while i <= n_int
        invariant
            1 <= i <= n_int + 1,
            result.len() == (i - 1) as nat,
            forall|j: int| 0 <= j < result.len() ==> result[j] == 'O' || result[j] == 'o',
            forall|j: int| 1 <= j < i ==> (is_fibonacci(j) <==> result[j-1] == 'O'),
            forall|j: int| 1 <= j < i ==> (!is_fibonacci(j) <==> result[j-1] == 'o'),
            n_int <= 100,
        decreases n_int - i + 1
    {
        let is_fib = if i == 1 || i == 2 {
            true
        } else if i == 3 || i == 5 || i == 8 || i == 13 || i == 21 || i == 34 || i == 55 || i == 89 {
            proof {
                lemma_is_fibonacci_values();
                if i == 3 {
                    assert(is_fibonacci(3));
                } else if i == 5 {
                    assert(is_fibonacci(5));
                } else if i == 8 {
                    assert(is_fibonacci(8));
                } else if i == 13 {
                    assert(is_fibonacci(13));
                } else if i == 21 {
                    assert(is_fibonacci(21));
                } else if i == 34 {
                    assert(is_fibonacci(34));
                } else if i == 55 {
                    assert(is_fibonacci(55));
                } else if i == 89 {
                    assert(is_fibonacci(89));
                }
            }
            true
        } else {
            proof {
                lemma_is_fibonacci_values();
                if i == 4 {
                    assert(!is_fibonacci(4));
                } else if i == 6 {
                    assert(!is_fibonacci(6));
                } else if i == 7 {
                    assert(!is_fibonacci(7));
                } else if i == 9 {
                    assert(!is_fibonacci(9));
                }
            }
            false
        };
        
        let c = if is_fib { 'O' } else { 'o' };
        
        proof {
            if is_fib {
                assert(is_fibonacci(i));
                assert(c == 'O');
            } else {
                assert(!is_fibonacci(i));
                assert(c == 'o');
            }
        }
        
        result.push(c);
        i = i + 1;
    }
    
    result
}
// </vc-code>


}

fn main() {}