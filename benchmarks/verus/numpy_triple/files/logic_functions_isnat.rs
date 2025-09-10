use vstd::prelude::*;

verus! {

#[derive(PartialEq, Eq, Clone, Copy)]
pub enum DateTime64 {
    Valid(i64),
    Nat,
}

fn isnat(x: Vec<DateTime64>) -> (result: Vec<bool>)
    ensures
        result.len() == x.len(),
        forall|i: int| 0 <= i < x.len() ==> 
            (result@.index(i) == true <==> x@.index(i) == DateTime64::Nat),
        forall|i: int| 0 <= i < x.len() ==> 
            (result@.index(i) == false <==> exists|val: i64| x@.index(i) == DateTime64::Valid(val)),
{
    assume(false);
    unreached();
}

}
fn main() {}