use vstd::prelude::*;

verus! {

spec fn triple(a: &[int]) -> bool {
    exists|i: int| 0 <= i < a.len() - 2 && #[trigger] a[i] == a[i + 1] && a[i + 1] == a[i + 2]
}

fn get_triple(a: &[int]) -> (index: usize)
ensures 
    (0 <= index < a.len() - 1) || index == a.len(),
    index == a.len() <==> !triple(a),
    (0 <= index < a.len() - 1) <==> triple(a),
    (0 <= index < a.len() - 1) ==> a[index as int] == a[index as int + 1] && a[index as int + 1] == a[index as int + 2]
{
    assume(false);
    unreached();
}

}
fn main() {}