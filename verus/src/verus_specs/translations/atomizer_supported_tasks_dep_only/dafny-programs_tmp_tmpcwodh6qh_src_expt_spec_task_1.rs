// ATOM 
spec fn Expt(b: int, n: nat) -> int
    requires n >= 0
{
    if n == 0 { 1 } else { b * Expt(b, n - 1) }
}

// SPEC 
pub fn expt(b: int, n: nat) -> (res: int)
    ensures(res == Expt(b, n))
{
}

// source: https://www.dcc.fc.up.pt/~nam/web/resources/vfs20/DafnyQuickReference.pdf
//ATOM_PLACEHOLDER_unknown_356 distributive(x: int, a: nat, b: nat) 
  ensures Expt(x, a) * Expt(x, b) == Expt(x, a + b)
pub fn distributive(x: int, a: nat, b: nat)
    ensures(Expt(x, a) * Expt(x, b) == Expt(x, a + b))
{
}