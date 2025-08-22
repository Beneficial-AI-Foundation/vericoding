use vstd::prelude::*;

verus! {
    // Factorial function
    spec fn fact(n: nat) -> nat
        decreases n
    {
        if n == 0 { 1 } else { n * fact((n - 1) as nat) }
    }

    // Accumulator-based factorial
    spec fn factAcc(n: nat, a: int) -> int
        decreases n
    {
        if n == 0 { a } else { factAcc((n - 1) as nat, n * a) }
    }

    // Alternative factorial using accumulator
    spec fn factAlt(n: nat) -> int {
        factAcc(n, 1)
    }

    // Proof that factAcc is correct
    proof fn factAcc_correct(n: nat, a: int)
        ensures factAcc(n, a) == a * fact(n)
        decreases n
    {
        if n == 0 {
            // Base case: factAcc(0, a) = a and fact(0) = 1, so a * fact(0) = a * 1 = a
            assert(factAcc(0, a) == a);
            assert(fact(0) == 1);
            assert(a * fact(0) == a * 1);
            assert(a * 1 == a) by (nonlinear_arith);
        } else {
            // Inductive step
            factAcc_correct((n - 1) as nat, n * a);
            // By induction hypothesis: factAcc((n-1), n*a) == (n*a) * fact(n-1)
            // We need to show: factAcc(n, a) == a * fact(n)
            // We have: factAcc(n, a) == factAcc((n-1), n*a) == (n*a) * fact(n-1)
            // And: a * fact(n) == a * (n * fact(n-1)) == (a * n) * fact(n-1) == (n * a) * fact(n-1)
            assert(factAcc(n, a) == factAcc((n - 1) as nat, n * a));
            assert(factAcc((n - 1) as nat, n * a) == (n * a) * fact((n - 1) as nat));
            assert(fact(n) == n * fact((n - 1) as nat));
            assert(a * fact(n) == a * (n * fact((n - 1) as nat)));
            // Use associativity of multiplication
            assert(a * (n * fact((n - 1) as nat)) == (a * n) * fact((n - 1) as nat)) by (nonlinear_arith);
            assert((a * n) * fact((n - 1) as nat) == (n * a) * fact((n - 1) as nat)) by (nonlinear_arith);
            assert(factAcc(n, a) == (n * a) * fact((n - 1) as nat));
            assert(a * fact(n) == (n * a) * fact((n - 1) as nat));
        }
    }

    // Proof that factAlt is correct
    proof fn factAlt_correct(n: nat)
        ensures factAlt(n) == fact(n)
    {
        factAcc_correct(n, 1);
        assert(factAcc(n, 1) == 1 * fact(n));
        assert(1 * fact(n) == fact(n)) by (nonlinear_arith);
        assert(factAlt(n) == factAcc(n, 1));
    }

    // List datatype
    pub enum List<T> {
        Nil,
        Cons(T, Box<List<T>>),
    }

    // Length function
    spec fn length<T>(l: List<T>) -> nat
        decreases l
    {
        match l {
            List::Nil => 0,
            List::Cons(_, r) => 1 + length(*r),
        }
    }

    // Proof that length is non-negative
    proof fn length_non_neg<T>(l: List<T>)
        ensures length(l) >= 0
        decreases l
    {
        match l {
            List::Nil => {},
            List::Cons(_, r) => {
                length_non_neg(*r);
                assert(length(*r) >= 0);
                assert(1 + length(*r) >= 0);
                assert(1 + length(*r) == length(l));
            }
        }
    }

    // Tail-recursive length function
    spec fn lengthTL<T>(l: List<T>, acc: nat) -> nat
        decreases l
    {
        match l {
            List::Nil => acc,
            List::Cons(_, r) => lengthTL(*r, 1 + acc),
        }
    }

    // Auxiliary lemma for lengthTL
    proof fn lengthTL_aux<T>(l: List<T>, acc: nat)
        ensures lengthTL(l, acc) == acc + length(l)
        decreases l
    {
        match l {
            List::Nil => {
                assert(acc + length::<T>(List::Nil) == acc);
            },
            List::Cons(_, r) => {
                lengthTL_aux(*r, acc + 1);
                assert(lengthTL(*r, acc + 1) == (acc + 1) + length(*r));
                assert(lengthTL(l, acc) == lengthTL(*r, acc + 1));
                assert(length(l) == 1 + length(*r));
                assert(acc + length(l) == acc + (1 + length(*r)));
                assert(acc + (1 + length(*r)) == (acc + 1) + length(*r)) by (nonlinear_arith);
            }
        }
    }

    // Proof that length and lengthTL are equivalent
    proof fn lengthEq<T>(l: List<T>)
        ensures length(l) == lengthTL(l, 0)
    {
        lengthTL_aux(l, 0);
        assert(lengthTL(l, 0) == 0 + length(l));
        assert(0 + length(l) == length(l)) by (nonlinear_arith);
    }
}

fn main() {}