use vstd::prelude::*;

verus! {

spec fn is_odd(n: i32) -> bool {
    n % 2 == 1
}

fn is_odd_at_index_odd(a: &Vec<i32>) -> (result: bool)
    ensures
        result <==> (forall|i: int| 0 <= i < a.len() && i % 2 == 1 ==> is_odd(a[i as int])),
{
    assume(false);
    unreached()
}

}
fn main() {}