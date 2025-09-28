use vstd::prelude::*;

verus! {

// <vc-helpers>
proof fn lemma_forall_lt<T>(seq: Seq<T>, i: int)
    requires 0 <= i <= seq.len()
    ensures forall j: int | 0 <= j < i ==> { seq.index(j) == seq@[j] }
{
    reveal(Seq::index);
    assert(forall j: int | 0 <= j < i ==> { seq@[j] == seq.index(j) });
}
// </vc-helpers>

// <vc-spec>
fn is_decimal_with_two_precision(s: &str) -> (result: bool)
    ensures
        result ==> exists|i: int| 0 <= i < s@.len() && s@[i] == '.' && s@.len() - i - 1 == 2,
        !result ==> !exists|i: int| 0 <= i < s@.len() && s@[i] == '.' && s@.len() - i - 1 == 2,
// </vc-spec>
// <vc-code>
{
    let len = s.len();
    let mut index = 0;
    while index < len
        invariant
            0 <= index <= len,
            forall|i: int| 0 <= i < index ==> { s@[i] == '.' ==> len - i - 1 != 2 }
    {
        let c = s@[index];
        if c == '.' {
            if len - index - 1 == 2 {
                return true;
            }
        }
        assert(forall|i: int| 0 <= i < index+1 ==> { s@[i] == '.' ==> len - i - 1 != 2 });
        index = index + 1;
    }
    false
}
// </vc-code>

fn main() {
}

}