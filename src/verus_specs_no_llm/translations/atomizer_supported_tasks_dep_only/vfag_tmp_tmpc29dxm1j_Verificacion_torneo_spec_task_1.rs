// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn torneo(Valores: array?<real>, i: int, j: int, k: int) -> pos_padre: int, pos_madre: int
    requires Valores != null and Valores.len() >= 20 and Valores.len() < 50 and i >= 0 and j >= 0 and k >= 0,
             i < Valores.len() and j < Valores.len() and k < Valores.len() and i != j and j != k and k != i
    ensures exists p, q, r | p in
{
}

}