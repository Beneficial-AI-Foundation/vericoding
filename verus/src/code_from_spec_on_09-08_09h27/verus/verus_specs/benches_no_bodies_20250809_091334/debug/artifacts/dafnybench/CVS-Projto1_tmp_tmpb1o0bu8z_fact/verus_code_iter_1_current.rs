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
            // Base case: factAcc(0, a) == a and fact(0) == 1
            // So factAcc(0, a) == a == a * 1 == a * fact(0)
        } else {
            // Inductive case: factAcc(n, a) == factAcc(n-1, n*a)
            // By IH: factAcc(n-1, n*a) == (n*a) * fact(n-1)
            //                            == a * n * fact(n-1)
            //                            == a * fact(n)
            factAcc_correct((n - 1) as nat, n * a);
        }
    }

    // Proof that factAlt is correct
    proof fn factAlt_correct(n: nat)
        ensures factAlt(n) == fact(n)
    {
        // factAlt(n) = factAcc(n, 1)
        // By factAcc_correct: factAcc(n, 1) == 1 * fact(n) == fact(n)
        factAcc_correct(n, 1);
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
            List::Nil => {
                // length(Nil) == 0 >= 0
            }
            List::Cons(_, r) => {
                // By IH: length(*r) >= 0
                // So length(Cons(_, r)) == 1 + length(*r) >= 1 + 0 == 1 >= 0
                length_non_neg(*r);
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
                // lengthTL(Nil, acc) == acc
                // acc + length(Nil) == acc + 0 == acc
            }
            List::Cons(_, r) => {
                // lengthTL(Cons(_, r), acc) == lengthTL(*r, 1 + acc)
                // By IH: lengthTL(*r, 1 + acc) == (1 + acc) + length(*r)
                //                                == acc + 1 + length(*r)
                //                                == acc + length(Cons(_, r))
                lengthTL_aux(*r, 1 + acc);
            }
        }
    }

    // Proof that length and lengthTL are equivalent
    proof fn lengthEq<T>(l: List<T>)
        ensures length(l) == lengthTL(l, 0)
    {
        // By lengthTL_aux: lengthTL(l, 0) == 0 + length(l) == length(l)
        lengthTL_aux(l, 0);
    }
}

fn main() {}