use vstd::prelude::*;

verus! {
    uninterp spec fn P(x: int) -> bool;

    uninterp spec fn Q(x: int) -> bool;

    fn test()
        requires forall|x: int| #[trigger] P(x) ==> P(x) && Q(x),
        ensures Q(0)
    {
    // TODO: Remove this comment and implement the function body
    }
}

fn main() {}