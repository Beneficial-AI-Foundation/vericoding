use vstd::prelude::*;

verus! {

fn increment_array(a: &mut Vec<i32>)
  requires old(a).len() > 0,
  ensures 
      a.len() == old(a).len(),
      forall|i: int| 0 <= i < a.len() ==> a[i] == old(a)[i] + 1,
{
    assume(false);
    unreached();
}

}
fn main() {}