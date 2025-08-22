use vstd::prelude::*;

verus! {
    uninterp spec fn P(x: int) -> bool;

    uninterp spec fn Q(x: int) -> bool;

    fn test()
        requires forall|x: int| #[trigger] P(x) ==> P(x) && Q(x),
        ensures Q(0)
    {
    }
}

fn main() {}