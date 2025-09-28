use vstd::prelude::*;

verus! {

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn contains_sequence(list: Seq<Seq<int>>, sub: Seq<int>) -> (result: bool)
    ensures result <==> exists|i: int| 0 <= i < list.len() && sub == list[i]
// </vc-spec>
// <vc-code>
{
    let mut i: nat = 0;
    let mut result = false;
    while i < list.len()
        invariant
            0 <= i as int <= list.len() as int,
            result == (exists|k: nat| #[trigger] list.index(k as int) == sub && 0 <= k as int && k as int < i as int),
    {
        if list.index(i as int) == sub {
            result = true;
            break;
        }
        i = (i + 1) as nat;
    }
    result
}
// </vc-code>

fn main() {
}

}