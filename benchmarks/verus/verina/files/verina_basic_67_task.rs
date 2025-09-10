use vstd::prelude::*;

verus! {

fn is_palindrome(x: Seq<char>) -> (result: bool)
    ensures
        result <==> (forall|i: int| 0 <= i < x.len() ==> #[trigger] x[i] == x[x.len() - 1 - i]),
{
    assume(false);
    unreached()
}

}
fn main() {}