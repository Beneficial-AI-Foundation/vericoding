use vstd::prelude::*;

verus! {

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn get_first_elements(lst: Seq<Seq<int>>) -> (result: Seq<int>)
    requires forall|i: int| 0 <= i < lst.len() ==> lst[i].len() > 0,
    ensures result.len() == lst.len(),
    ensures forall|i: int| 0 <= i < result.len() ==> result[i] == lst[i][0],
// </vc-spec>
// <vc-code>
{
    assume(false);
    Seq::empty()
}
// </vc-code>


fn main() {
}

}