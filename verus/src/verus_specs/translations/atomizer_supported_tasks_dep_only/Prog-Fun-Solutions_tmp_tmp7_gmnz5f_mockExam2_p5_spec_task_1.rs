// problem 5:
// name:      Gabriele Berardi
// s-number: s4878728
// table:     XXXX

// ATOM 
// problem 5:
// name:      Gabriele Berardi
// s-number: s4878728
// table:     XXXX

spec fn f(n: int) -> int {
    if n < 0 { 0 } else { 3 * f(n - 5) + n }
}

// SPEC 

pub fn problem5(n: nat) -> (x: int)
    ensures(x == f(n))
{
}