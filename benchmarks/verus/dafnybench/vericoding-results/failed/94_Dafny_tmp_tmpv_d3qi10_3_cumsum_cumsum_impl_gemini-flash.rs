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
proof fn sum_properties(a: Seq<i32>, i: int)
    requires
        0 <= i < a.len(),
    ensures
        sum(a, i) == ({
            let mut s: int = 0;
            let mut j: int = 0;
            while j <= i
                invariant
                    0 <= j <= i + 1,
                    s == sum(a, j - 1),
                    j > 0 ==> s == sum(a, j - 1),
                    j == 0 ==> s == 0,
                    0 <= j <= a.len(),
                    (j > 0 ==> 0 <= j - 1 < a.len()),
            {
                s = s + a[j] as int;
                j = j + 1;
            }
            s
        }),
{
    if i == 0 {
        assert(sum(a, 0) == a[0] as int);
    } else {
        sum_properties(a, i - 1);
        assert(sum(a, i) == a[i] as int + sum(a, i - 1));
    }
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
    assert(n > 0);

    b[0] = a[0];
    assert(b[0] as int == sum(a@, 0));

    let mut i: usize = 1;

    while i < n
        invariant
            1 <= i && i <= n,
            n == a.len(),
            n == b.len(),
            forall|j: int| 0 <= j && j < i as int ==> b[j as usize] as int == sum(a@, j),
    {
        b[i as usize] = b[(i - 1) as usize] + a[i as usize];

        assert(b[(i - 1) as usize] as int == sum(a@, (i - 1) as int));
        assert(b[i as usize] as int == sum(a@, (i - 1) as int) + a[i as usize] as int);

        proof {
            sum_properties(a@, i as int);
            assert(sum(a@, i as int) == a@[i as int] as int + sum(a@, (i - 1) as int));
        }
        assert(b[i as usize] as int == sum(a@, i as int));

        i = i + 1;
    }
}
// </vc-code>

fn main() {}

}