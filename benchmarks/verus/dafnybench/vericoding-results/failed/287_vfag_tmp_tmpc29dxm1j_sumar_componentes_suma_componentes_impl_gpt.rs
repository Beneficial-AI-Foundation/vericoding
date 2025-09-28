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
proof fn lemma_sub_add_cancel(x: int, y: int, z: int)
    ensures x - (y + z) + y == x - z
{
    assert(x - (y + z) + y == x - y - z + y);
    assert(x - y - z + y == x - z + (-y + y));
    assert(-y + y == 0);
    assert(x - z + 0 == x - z);
}

proof fn lemma_suma_unfold_lt(V: &[i32], n: int)
    requires 0 <= n < V.len() as int
    ensures suma_aux(V, n) == V[n as int] + suma_aux(V, n + 1)
{
    reveal_with_fuel(suma_aux, 1);
    assert(suma_aux(V, n) == V[n as int] + suma_aux(V, n + 1));
}

proof fn lemma_suma_at_len(V: &[i32])
    ensures suma_aux(V, V.len() as int) == 0
{
    reveal_with_fuel(suma_aux, 1);
    assert(suma_aux(V, V.len() as int) == 0);
}

proof fn lemma_index_slice_i32_int_equiv(V: &[i32], i: usize)
    requires i < V.len()
    ensures V[i as int] == V[i] as int
{
    assert(V[i as int] == V[i] as int);
}
// </vc-helpers>

// <vc-spec>
fn suma_componentes(V: &[i32]) -> (suma: i32)
    ensures suma == suma_aux(V, 0)
// </vc-spec>
// <vc-code>
{
    let mut i: usize = 0;
    let mut acc: i32 = 0;
    while i < V.len()
        invariant
            0 <= i as int <= V.len() as int,
            acc as int == suma_aux(V, 0) - suma_aux(V, i as int),
        decreases V.len() as int - i as int
    {
        let old_i = i;
        let old_acc = acc;

        assert(old_i < V.len());
        proof {
            assert(0 <= old_i as int);
            assert(old_i as int < V.len() as int);
            lemma_suma_unfold_lt(V, old_i as int);
            assert(suma_aux(V, old_i as int) == V[old_i as int] + suma_aux(V, old_i as int + 1));

            let xi = suma_aux(V, 0);
            let yi = V[old_i as int];
            let zi = suma_aux(V, old_i as int + 1);

            assert(suma_aux(V, old_i as int) == yi + zi);
            assert(xi - suma_aux(V, old_i as int) == xi - (yi + zi));
            assert(old_acc as int == xi - suma_aux(V, old_i as int));
            assert(old_acc as int + yi == xi - (yi + zi) + yi);
            lemma_sub_add_cancel(xi, yi, zi);
            assert(old_acc as int + yi == xi - zi);

            lemma_index_slice_i32_int_equiv(V, old_i);
            assert(yi == V[old_i] as int);
            assert(old_acc as int + (V[old_i] as int) == suma_aux(V, 0) - suma_aux(V, old_i as int + 1));
        }

        acc = old_acc + V[old_i];
        i = old_i + 1;
    }
    proof {
        assert(!(i < V.len()));
        assert(i as int <= V.len() as int);
        assert(i >= V.len());
        assert(i as int >= V.len() as int);
        assert(i as int == V.len() as int);

        lemma_suma_at_len(V);
        assert(suma_aux(V, V.len() as int) == 0);
        assert(acc as int == suma_aux(V, 0) - suma_aux(V, i as int));
        assert(acc as int == suma_aux(V, 0) - 0);
        assert(acc as int == suma_aux(V, 0));
    }
    acc
}
// </vc-code>

fn main() {}

}