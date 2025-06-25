// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn suma_componentes(V: array?<int>) -> (suma: int)
    requires V != null
    ensures suma == suma_aux(V, 0)	// x = V[0] + V[1] + ... + V[N - 1]
{
}

}