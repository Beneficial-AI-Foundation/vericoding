use vstd::prelude::*;

verus! {

spec fn is_divisible_by_11_precond(n: int) -> bool {
    true
}

fn is_divisible_by_11(n: i64) -> (result: bool)
    requires is_divisible_by_11_precond(n as int)
    ensures (result ==> exists|k: int| #[trigger] (11 * k) == n as int) &&
            (!result ==> forall|k: int| #[trigger] (11 * k) != n as int)
{
    n % 11 == 0
}

fn main() {}

}