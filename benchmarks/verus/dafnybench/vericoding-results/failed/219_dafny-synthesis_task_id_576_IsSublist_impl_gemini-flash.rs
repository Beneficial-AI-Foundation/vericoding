use vstd::prelude::*;

verus! {

// <vc-helpers>
fn subrange_equal(s1: &Seq<int>, s2: &Seq<int>, start: int) -> bool
    requires
        0 <= start,
        start + s2.len() as int <= s1.len() as int,
    ensures
        s1.subrange(start, start + s2.len() as int) =~= *s2,
{
    let mut i: nat = 0; // Changed to nat
    while (i as int) < s2.len() as int // Cast i to int for comparison
        invariant
            0 <= i as int && (i as int) <= s2.len() as int,
            s1.subrange(start, start + i as int) =~= s2.subrange(0, i as int),
    {
        if s1.index(start + i as int) != s2.index(i as int) {
            return false;
        }
        i = (i + 1) as nat; // Cast back to nat
    }
    true
}
// </vc-helpers>

// <vc-spec>
fn is_sublist(sub: Seq<int>, main: Seq<int>) -> (result: bool)
    ensures
        result == exists|i: int, j: int| 0 <= i <= main.len() - sub.len() && j == i + sub.len() && sub =~= #[trigger] main.subrange(i, j)
// </vc-spec>
// <vc-code>
{
    if sub.len() == 0 {
        return true;
    }

    if sub.len() > main.len() {
        return false;
    }

    let mut i: nat = 0; // Changed to nat
    while (i as int) <= (main.len() as int - sub.len() as int) // Cast i to int for comparison
        invariant
            0 <= i as int && (i as int) <= main.len() as int - sub.len() as int + 1,
            forall|k: int| 0 <= k < i as int ==> sub != #[trigger] main.subrange(k, k + sub.len() as int),
    {
        if subrange_equal(&main, &sub, i as int) { // Cast i to int
            return true;
        }
        i = (i + 1) as nat; // Cast back to nat
    }
    false
}
// </vc-code>

fn main() {
}

}