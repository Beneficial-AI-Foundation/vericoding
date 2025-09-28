use vstd::prelude::*;

verus! {

// <vc-helpers>
//
// </vc-helpers>

// <vc-spec>
fn is_sublist(sub: Seq<int>, main: Seq<int>) -> (result: bool)
    ensures
        result == exists|i: int, j: int| 0 <= i <= main.len() - sub.len() && j == i + sub.len() && sub =~= #[trigger] main.subrange(i, j)
// </vc-spec>
// <vc-code>
{
    if (sub.len() as usize) > (main.len() as usize) {
        return false;
    }
    let max_i = (main.len() as usize) - (sub.len() as usize);
    let mut i: usize = 0;
    while i <= max_i
        invariant
            0 <= i <= max_i + 1,
            forall |k: int| 0 <= k < i ==> !(sub =~= #[trigger] main.subrange(k, k + (sub.len() as int))),
    {
        let j: usize = i + (sub.len() as usize);
        let i_int = ghost(i as int);
        let j_int = ghost(j as int);
        if sub =~= main.subrange(i_int, j_int) {
            return true;
        }
        i = i + 1;
    }
    proof {
        assert(forall |k: int| 0 <= k && k < (main.len() as int) - (sub.len() as int) + 1 ==> !(sub =~= #[trigger] main.subrange(k, k + (sub.len() as int))));
    }
    false
}
// </vc-code>

fn main() {
}

}