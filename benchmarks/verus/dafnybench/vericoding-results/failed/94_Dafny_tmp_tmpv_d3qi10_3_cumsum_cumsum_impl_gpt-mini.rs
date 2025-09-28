use vstd::prelude::*;

verus! {

spec fn sum(a: Seq<i32>, i: int) -> int
    recommends 
        0 <= i < a.len(),
    decreases i
{
    if 0 <= i < a.len() {
        a[i] as int + if i == 0 { 0 } else { sum(a, i - 1) }
    } else {
        0
    }
}

// <vc-helpers>
proof fn sum_rec_lemma(a: Seq<i32>, i: int)
    requires 0 <= i < a.len()
    decreases i
{
    if i == 0 {
        // sum(a,0) == a[0] as int + 0 by definition
    } else {
        sum_rec_lemma(a, i - 1);
    }
    assert(sum(a, i) == a[i] as int + if i == 0 { 0 } else { sum(a, i - 1) });
}

proof fn int_cast_add(x: i32, y: i32)
{
    assert((x + y) as int == x as int + y as int);
}
// </vc-helpers>

// <vc-spec>
fn cumsum(a: &[i32], b: &mut [i32])
    requires 
        a.len() == old(b).len(),
        a.len() > 0,
    ensures 
        forall|i: int| 0 <= i < a.len() ==> b[i] as int == sum(a@, i),
// </vc-spec>
// <vc-code>
{
    let n = a.len();
    let mut i: usize = 0;
    while (i < n)
        invariant { 0 <= i as int && i as int <= n as int }
        invariant { forall |j: int| (0 <= j && j < i as int) ==> b[j as usize] as int == sum(a@, j) }
    {
        if i == 0 {
            b[0] = a[0];
            proof {
                // prove b[0] as int == sum(a@, 0)
                sum_rec_lemma(a@, 0);
                assert(b[0] as int == a[0] as int);
                assert(a[0] as int == sum(a@, 0));
            }
        } else {
            let pi: usize = i - 1;
            let tmp: i32 = b[pi] + a[i];
            b[i] = tmp;
            proof {
                // instantiate loop condition facts to use sum_rec_lemma
                assert(0 <= i as int && i as int < n as int);
                // from invariant: b[pi] as int == sum(a@, pi)
                assert(pi as int + 1 == i as int);
                assert(0 <= pi as int && pi as int < i as int);
                assert(b[pi] as int == sum(a@, pi as int));
                // relate (b[pi] + a[i]) as int to b[pi] as int + a[i] as int
                int_cast_add(b[pi], a[i]);
                // sum(a, i) == a[i] as int + sum(a, i-1)
                sum_rec_lemma(a@, i as int);
                // chain equalities to conclude b[i] as int == sum(a@, i)
                assert(b[i] as int == (b[pi] + a[i]) as int);
                assert((b[pi] + a[i]) as int == b[pi] as int + a[i] as int);
                assert(b[pi] as int + a[i] as int == sum(a@, pi as int) + a[i] as int);
                assert(sum(a@, pi as int) + a[i] as int == sum(a@, i as int));
            }
        }
        i += 1;
    }
}
// </vc-code>

fn main() {}

}