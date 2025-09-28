// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(n: int) -> bool {
    100 <= n <= 999
}

spec fn contains_seven(n: int) -> bool
    recommends valid_input(n)
{
    (n % 10) == 7 || ((n / 10) % 10) == 7 || (n / 100) == 7
}

spec fn valid_output(result: Seq<char>) -> bool {
    result == "Yes\n"@ || result == "No\n"@
}
// </vc-preamble>

// <vc-helpers>
proof fn lemma_contains_seven_def(n: int)
    requires
        valid_input(n),
    ensures
        contains_seven(n) == ((n % 10) == 7 || ((n / 10) % 10) == 7 || (n / 100) == 7),
{
}

// </vc-helpers>

// <vc-spec>
fn solve(n: i8) -> (result: Vec<char>)
    requires valid_input(n as int)
    ensures 
        valid_output(result@) &&
        ((result@ == "Yes\n"@) <==> contains_seven(n as int))
// </vc-spec>
// <vc-code>
{
    let ni: int = n as int;

    let d1: int = ni % 10;
    let d2: int = (ni / 10) % 10;
    let d3: int = ni / 100;

    let has7: bool = d1 == 7 || d2 == 7 || d3 == 7;

    let result: Vec<char>;
    if has7 {
        result = Vec::<char>::from_seq("Yes\n"@);
        assert(result@ == "Yes\n"@);
        assert(valid_output(result@));
    } else {
        result = Vec::<char>::from_seq("No\n"@);
        assert(result@ == "No\n"@);
        assert(valid_output(result@));
    }

    proof {
        lemma_contains_seven_def(ni);
        assert(has7 <==> contains_seven(ni));
        if has7 {
            assert(result@ == "Yes\n"@);
            assert((result@ == "Yes\n"@) <==> has7);
        } else {
            assert(result@ == "No\n"@);
            assert((result@ == "Yes\n"@) <==> has7);
        }
    }

    result
}

// </vc-code>


}

fn main() {}