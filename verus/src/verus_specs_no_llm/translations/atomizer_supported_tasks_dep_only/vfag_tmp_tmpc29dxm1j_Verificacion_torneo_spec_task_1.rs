// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn spec_torneo(Valores: array?<real>, i: int, j: int, k: int) -> pos_padre : int, pos_madre : int
    requires
        Valores != null && Valores.len() >= 20 && Valores.len() < 50 && i >= 0 && j >= 0 && k >= 0,
        i < Valores.len() && j < Valores.len() && k < Valores.len() && i != j && j != k && k != i
    ensures
        exists p, q, r | p in
;

proof fn lemma_torneo(Valores: array?<real>, i: int, j: int, k: int) -> (pos_padre: int, pos_madre: int)
    requires
        Valores != null && Valores.len() >= 20 && Valores.len() < 50 && i >= 0 && j >= 0 && k >= 0,
        i < Valores.len() && j < Valores.len() && k < Valores.len() && i != j && j != k && k != i
    ensures
        exists p, q, r | p in
{
    (0, 0)
}

}