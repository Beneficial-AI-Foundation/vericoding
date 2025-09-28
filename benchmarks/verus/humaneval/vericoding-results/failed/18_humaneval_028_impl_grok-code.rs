// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn concat_strings(strings: Seq<Seq<char>>, index: nat) -> Seq<char>
    decreases strings.len() - index
{
    if index >= strings.len() {
        Seq::<char>::empty()
    } else {
        strings[index as int] + concat_strings(strings, index + 1)
    }
}
// </vc-preamble>

// <vc-helpers>
spec fn concat_prefix(strings: Seq<Seq<char>>, up_to: int) -> Seq<char>
    decreases up_to
    requires 0 <= up_to <= strings.len()
{
    if up_to == 0 {
        Seq::<char>::empty()
    } else {
        concat_prefix(strings, up_to - 1) + strings[up_to - 1 as int]
    }
}
// </vc-helpers>

// <vc-spec>
fn concatenate(strings: Vec<Vec<char>>) -> (result: Vec<char>)
    ensures 
        result@ == concat_strings(strings@.map(|i, s: Vec<char>| s@), 0) &&
        (strings@.len() == 0 ==> result@ == Seq::<char>::empty())
// </vc-spec>
// <vc-code>
{
    let mut result: Vec<char> = Vec::new();
    let mut i: int = 0;
    proof {
        assert(result@ == concat_prefix(strings@.map(|idx: int, s: Vec<char>| s@), 0));
    }
    while i < strings.len()
        invariant
            0 <= i <= strings.len(),
            result@ == concat_prefix(strings@.map(|idx: int, s: Vec<char>| s@), i)
        decreases strings.len() - i as nat
    {
        let inner = &strings[i];
        let mut j: int = 0;
        while j < inner.len()
            invariant
                j <= inner.len(),
                result@ == concat_prefix(strings@.map(|idx: int, s: Vec<char>| s@), i) + inner@[0..j]
            decreases inner.len() - j as nat
        {
            result.push(inner@[j]);
            proof {
                assert(result@[result.len() - 1] == inner@[j]);
                assert(result@.take(result.len() - 1) == concat_prefix(strings@.map(|idx: int, s: Vec<char>| s@), i) + inner@[0..j]);
            }
            j += 1;
        }
        proof {
            assert(concat_prefix(strings@.map(|idx: int, s: Vec<char>| s@), i) + inner@[0..inner.len()] + concat_prefix(strings@.map(|idx: int, s: Vec<char>| s@), i + 1));
        }
        i += 1;
    }
    proof {
        assert(result@ == concat_prefix(strings@.map(|idx: int, s: Vec<char>| s@), strings@.len()));
    }
}
// </vc-code>


}

fn main() {}