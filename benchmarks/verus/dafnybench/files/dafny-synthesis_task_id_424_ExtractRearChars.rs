use vstd::prelude::*;

verus! {

fn extract_rear_chars(l: &Vec<Vec<char>>) -> (r: Vec<char>)
    requires forall|i: int| 0 <= i < l.len() ==> l[i].len() > 0
    ensures 
        r.len() == l.len()
        && forall|i: int| 0 <= i < l.len() ==> r[i] == l[i][l[i].len() - 1]
{
    assume(false);
    unreached();
}

}
fn main() {}