// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
pub open spec fn is_valid_value(x: i8) -> bool
{
    x % 2 == 0 && (x == 2 || x == 4 || x == 6 || x == 8)
}

pub open spec fn is_valid_result(s: Seq<i8>) -> bool
{
    forall|i:int| 0 <= i < s.len() ==> is_valid_value(s[i])
}

proof fn lemma_empty_seq_is_valid()
    ensures is_valid_result(Seq::<i8>::empty())
{
}

// </vc-helpers>

// <vc-spec>
fn generate_integers(a: i8, b: i8) -> (result: Vec<i8>)
    ensures (forall|i: int| 0 <= i < result@.len() ==> result@[i] % 2 == 0) &&
            (forall|i: int| 0 <= i < result@.len() ==> (result@[i] == 2 || result@[i] == 4 || result@[i] == 6 || result@[i] == 8))
// </vc-spec>
// <vc-code>
{
    Vec::new()
}
// </vc-code>


}

fn main() {}