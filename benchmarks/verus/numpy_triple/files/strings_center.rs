use vstd::prelude::*;

verus! {

fn center(a: Vec<String>, width: Vec<usize>, fillchar: char) -> (result: Vec<String>)
    requires 
        a.len() == width.len(),
    ensures 
        result.len() == a.len(),
        forall|i: int| 0 <= i < result.len() ==> 
            #[trigger] result[i]@.len() >= 0 && {
                let orig_len = a[i]@.len() as int;
                let target_width = width[i] as int;
                &&& (orig_len >= target_width ==> result[i] == a[i])
                &&& result[i]@.len() as int == if orig_len >= target_width { orig_len } else { target_width }
            }
{
    assume(false);
    unreached()
}

}
fn main() {}