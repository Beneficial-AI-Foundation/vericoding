// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(input: Seq<char>) -> bool {
    input.len() == 3 && forall|i: int| 0 <= i < input.len() ==> input[i] == 'A' || input[i] == 'B'
}

spec fn bus_service_exists(input: Seq<char>) -> bool
    recommends valid_input(input)
{
    input[0] != input[1] || input[1] != input[2]
}
// </vc-preamble>

// <vc-helpers>
proof fn lemma_bus_spec_equiv(input: &Vec<char>)
    requires
        valid_input(input@),
    ensures
        bus_service_exists(input@) == ((input[0] != input[1]) || (input[1] != input[2])),
{
    assert(input@.len() == 3);
    assert(input.len() == input@.len());
    assert(0 <= 0 && 0 < input.len());
    assert(0 <= 1 && 1 < input.len());
    assert(0 <= 2 && 2 < input.len());
    assert(input@[0] == input[0]);
    assert(input@[1] == input[1]);
    assert(input@[2] == input[2]);
    assert(bus_service_exists(input@) == ((input[0] != input[1]) || (input[1] != input[2])));
}
// </vc-helpers>

// <vc-spec>
fn solve(input: Vec<char>) -> (result: Vec<char>)
    requires
        valid_input(input@),
    ensures
        result@ == seq!['Y', 'e', 's'] <==> bus_service_exists(input@),
        result@ == seq!['Y', 'e', 's'] || result@ == seq!['N', 'o'],
// </vc-spec>
// <vc-code>
{
    proof {
        assert(input@.len() == 3);
        assert(input.len() == input@.len());
    }
    assert(0 < input.len());
    assert(1 < input.len());
    assert(2 < input.len());
    let b = (input[0] != input[1]) || (input[1] != input[2]);
    proof {
        lemma_bus_spec_equiv(&input);
        assert(bus_service_exists(input@) == ((input[0] != input[1]) || (input[1] != input[2])));
        assert(b == ((input[0] != input[1]) || (input[1] != input[2])));
    }
    let mut res: Vec<char> = Vec::new();
    if b {
        res.push('Y');
        res.push('e');
        res.push('s');
        proof { assert(res@ == seq!['Y', 'e', 's']); }
    } else {
        res.push('N');
        res.push('o');
        proof { assert(res@ == seq!['N', 'o']); }
    }
    res
}
// </vc-code>


}

fn main() {}