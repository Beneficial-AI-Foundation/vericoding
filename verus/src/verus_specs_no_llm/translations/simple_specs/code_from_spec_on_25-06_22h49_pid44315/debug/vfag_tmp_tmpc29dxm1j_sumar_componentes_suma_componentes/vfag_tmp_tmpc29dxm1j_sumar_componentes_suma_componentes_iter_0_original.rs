// Translated from Dafny
use builtin::*;
use builtin_macros::*;

use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn suma_componentes(V: array?<int>) -> (suma: int)
    requires
        V != null
    ensures
        suma == suma_aux(V, 0)	// x = V.spec_index(0) + V.spec_index(1) + ... + V.spec_index(N - 1)
{
    return 0;
}

}