use vstd::prelude::*;

verus! {

spec fn suma_aux(V: &[i32], n: int) -> int
    decreases V.len() - n
    when 0 <= n <= V.len()
{
    if n == V.len() {
        0
    } else {
        V[n as int] + suma_aux(V, n + 1)
    }
}

// <vc-helpers>
proof fn suma_aux_unfold(V: &[i32], n: int)
    requires 0 <= n && n < (V.len() as int)
    ensures suma_aux(V, n) == (V[n as usize] as int) + suma_aux(V, n + 1)
    decreases (V.len() as int) - n
{
    if n == (V.len() as int) - 1 {
        // by definition of suma_aux when n == V.len() - 1
    } else {
        suma_aux_unfold(V, n + 1);
    }
}

proof fn suma_aux_base(V: &[i32])
    ensures suma_aux(V, V.len() as int) == 0
{
    // by definition of suma_aux when n == V.len()
}
// </vc-helpers>

// <vc-spec>
fn suma_componentes(V: &[i32]) -> (suma: i32)
    ensures suma == suma_aux(V, 0)
// </vc-spec>
// <vc-code>
{
    let mut i: int = 0;
    let mut acc: i32 = 0;
    while i < V.len() as int
        invariant 0 <= i && i <= V.len() as int;
        invariant (acc as int) + suma_aux(V, i) == suma_aux(V, 0);
        decreases (V.len() as int) - i;
    {
        let old_i = i;
        let old_acc = acc;
        let vi = V[old_i as usize];
        // update state
        i = old_i + 1;
        acc = old_acc + vi;
        proof {
            // old_i < V.len() because of loop guard
            assert(old_i < V.len() as int);
            // unfold suma_aux at index old_i
            suma_aux_unfold(V, old_i);
            // use the loop invariant before the update
            assert((old_acc as int) + suma_aux(V, old_i) == suma_aux(V, 0));
            // combine to establish the invariant after the update
            assert((old_acc as int) + ((vi as int) + suma_aux(V, old_i + 1)) == suma_aux(V, 0));
            assert(((old_acc + vi) as int) + suma_aux(V, old_i + 1) == suma_aux(V, 0));
        }
    }
    proof {
        // At loop exit, i == V.len()
        assert(i == V.len() as int);
        // suma_aux(V, V.len()) == 0 by definition
        suma_aux_base(V);
        assert(suma_aux(V, i) == 0);
        // from invariant, (acc as int) + 0 == suma_aux(V, 0)
        assert((acc as int) + suma_aux(V, i) == suma_aux(V, 0));
    }
    acc
}
// </vc-code>

fn main() {}

}