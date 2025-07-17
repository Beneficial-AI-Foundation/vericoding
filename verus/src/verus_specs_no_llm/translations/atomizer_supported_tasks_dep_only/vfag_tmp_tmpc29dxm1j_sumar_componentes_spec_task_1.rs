// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn suma_aux(V: array?<int>, n: int) -> int

  // suma_aux(V, n) = V[n] + V[n + 1] + ... + V[N - 1]
    requires
        V != null			// P_0,
        0 <= n <= V.len()		// Q_0
  
  
  reads V
{
    (0, 0)
}

spec fn spec_suma_componentes(V: array?<int>) -> suma : int
    requires
        V != null
    ensures
        suma == suma_aux(V, 0)	// x = V.index(0) + V.index(1) + ... + V.index(N - 1)
;

proof fn lemma_suma_componentes(V: array?<int>) -> (suma: int)
    requires
        V != null
    ensures
        suma == suma_aux(V, 0)	// x = V.index(0) + V.index(1) + ... + V.index(N - 1)
{
    0
}

}