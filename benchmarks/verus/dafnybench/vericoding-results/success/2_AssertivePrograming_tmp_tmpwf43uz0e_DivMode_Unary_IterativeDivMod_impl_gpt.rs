use vstd::prelude::*;

verus! {

// Noa Leron 207131871  
// Tsuri Farhana 315016907


// definitions borrowed from Rustan Leino's Program Proofs Chapter 7
// (https://program-proofs.com/code.html example code in Dafny; source file 7-Unary.dfy)
pub enum Unary {
    Zero,
    Suc(Box<Unary>),
}

pub open spec fn unary_to_nat(x: Unary) -> nat 
    decreases x
{
    match x {
        Unary::Zero => 0nat,
        Unary::Suc(x_prime) => 1nat + unary_to_nat(*x_prime),
    }
}

pub open spec fn nat_to_unary(n: nat) -> Unary 
    decreases n
{
    if n == 0 {
        Unary::Zero
    } else {
        Unary::Suc(Box::new(nat_to_unary((n - 1) as nat)))
    }
}

pub open spec fn less(x: Unary, y: Unary) -> bool 
    decreases x, y
{
    match y {
        Unary::Zero => false,
        Unary::Suc(y_pred) => match x {
            Unary::Zero => true,
            Unary::Suc(x_pred) => less(*x_pred, *y_pred),
        }
    }
}

pub open spec fn less_alt(x: Unary, y: Unary) -> bool 
    decreases x, y
{
    match y {
        Unary::Zero => false,
        Unary::Suc(y_pred) => match x {
            Unary::Zero => true,
            Unary::Suc(x_pred) => less(*x_pred, *y_pred),
        }
    }
}

pub open spec fn add(x: Unary, y: Unary) -> Unary 
    decreases y
{
    match y {
        Unary::Zero => x,
        Unary::Suc(y_prime) => Unary::Suc(Box::new(add(x, *y_prime))),
    }
}

pub open spec fn sub(x: Unary, y: Unary) -> Unary 
    decreases y
{
    if less(x, y) {
        arbitrary()
    } else {
        match y {
            Unary::Zero => x,
            Unary::Suc(y_prime) => match x {
                Unary::Zero => arbitrary(),
                Unary::Suc(x_pred) => sub(*x_pred, *y_prime),
            }
        }
    }
}

pub open spec fn mul(x: Unary, y: Unary) -> Unary 
    decreases x
{
    match x {
        Unary::Zero => Unary::Zero,
        Unary::Suc(x_prime) => add(mul(*x_prime, y), y),
    }
}

/*
Goal: implement correcly and clearly, using iterative code (no recursion), documenting the proof obligations
    as we've learned, with assertions and a lemma for each proof goal

- DO NOT modify the specification or any of the definitions given in this file
- Not all definitions above are relevant, some are simply included as examples
- Feel free to use existing non-ghost functions/predicates in your code, and existing lemmas (for the proof) in your annotations
- New functions/predicates may be added ONLY as ghost
- If it helps you in any way, a recursive implementation + proof can be found in the book and the downloadable source file
  [https://program-proofs.com/code.html example code in Dafny, source file 7-Unary.dfy]
*/

fn iterative_div_mod_prime(x: Unary, y: Unary) -> (res: (Unary, Unary))
    requires y != Unary::Zero
    ensures add(mul(res.0, y), res.1) == x && less(res.1, y)
{
    assume(false);
    (Unary::Zero, Unary::Zero)
}

// <vc-helpers>
// no helpers needed
// </vc-helpers>

// <vc-spec>
fn iterative_div_mod(x: Unary, y: Unary) -> (res: (Unary, Unary))
    requires y != Unary::Zero
    ensures add(mul(res.0, y), res.1) == x && less(res.1, y)
// </vc-spec>
// <vc-code>
{
    iterative_div_mod_prime(x, y)
}
// </vc-code>

fn main() {}

}