use vstd::prelude::*;

spec fn contains_nothing_but_5(s: Set<int>) -> bool {
    forall|q: int| s.contains(q) ==> q == 5
}

spec fn yeah_contains_5(s: Set<int>) -> bool {
    exists|q: int| s.contains(q) && q == 5
}

spec fn via_set_comprehension(s: Set<int>) -> bool {
    Set::new(|q: int| s.contains(q) && q == 5).len() != 0
}

spec fn lambda_test(s: Set<int>) -> bool {
    (|q: int| s.contains(q))(5)
}

spec fn via_map_comprehension(s: Set<int>) -> bool {
    Map::new(|q: int| s.contains(q) && q == 5, |q: int| true).dom().len() != 0
}

spec fn contains_5(s: Set<int>) -> bool {
    {
        let q = 5;
        s.contains(q)
    }
}

enum R {
    MakeR(int),
    Other,
}

spec fn r_is_5(r: R) -> bool {
    match r {
        R::MakeR(q) => q == 5,
        R::Other => false,
    }
}

proof fn nonempty_set(x: int, s: Set<int>)
    requires(s.contains(x))
    ensures(s.len() != 0)
{
}

proof fn nonempty_map(x: int, s: Map<int, bool>)
    requires(s.dom().contains(x))
    ensures(s.len() != 0)
{
}

pub fn m(s: Set<int>, r: R, q: int)
    requires(
        s == Set::empty() && r == R::MakeR(5)
    )
{
}