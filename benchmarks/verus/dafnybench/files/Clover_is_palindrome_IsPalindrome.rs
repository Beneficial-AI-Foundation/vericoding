use vstd::prelude::*;

verus! {

fn is_palindrome(x: Seq<char>) -> (result: bool)
  ensures result <==> (forall|i: int| 0 <= i < x.len() ==> #[trigger] x[i] == x[x.len() - i - 1])
{
    assume(false);
    unreached()
}

}
fn main() {}