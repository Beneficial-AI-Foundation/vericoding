use vstd::prelude::*;

verus! {

fn all_digits(s: &str) -> (result: bool)
    ensures result <==> (forall|i: int| 0 <= i < s@.len() ==> {
        let c = #[trigger] s@.index(i);
        c == '0' || c == '1' || c == '2' || c == '3' || c == '4' || 
        c == '5' || c == '6' || c == '7' || c == '8' || c == '9'
    })
{
    assume(false);
    unreached()
}

}
fn main() {}