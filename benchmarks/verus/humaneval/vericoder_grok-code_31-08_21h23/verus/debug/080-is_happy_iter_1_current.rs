use vstd::prelude::*;

verus! {

spec fn three_distinct_spec(s: Seq<char>, i: int) -> (ret:bool)
    recommends
        0 < i && i + 1 < s.len(),
{
    (s[i - 1] != s[i]) && (s[i] != s[i + 1]) && (s[i] != s[i + 1])
}
// pure-end
spec fn happy_spec(s: Seq<char>) -> (ret:bool) {
    s.len() >= 3 && (forall|i: int| 0 < i && i + 1 < s.len() ==> three_distinct_spec(s, i))
}
// pure-end

// <vc-helpers>
// No additional helpers needed
// </vc-helpers>

// <vc-spec>
#[verifier::loop_isolation(false)]
fn is_happy(s: &Vec<char>) -> (happy: bool)
    // post-conditions-start
    ensures
        happy <==> happy_spec(s@),
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    let sl = s.len();
    if sl < 3 {
        return false;
    }
    let mut i = 1;
    let mut is_happy_flag = true;
    while i < sl - 1
        invariant
            1 <= i <= sl,
            is_happy_flag ==> (forall|j: int| 1 <= j < i ==> three_distinct_spec(s@, j)),
            !is_happy_flag ==> !(forall|j: int| 1 <= j < i ==> three_distinct_spec(s@, j)),
        decreases sl - i,
    {
        proof {
            assert(0 < i && i + 1 < sl);
        }
        let a = s[i - 1];
        let b = s[i];
        let c = s[i + 1];
        if !(a != b && b != c && a != c) {
            is_happy_flag = false;
        }
        proof {
            if is_happy_flag {
                assert(three_distinct_spec(s@, i));
            }
        }
        i += 1;
    }
    proof {
        assert(is_happy_flag ==> (forall|j: int| 0 < j < sl ==> #[trigger] three_distinct_spec(s@, j)));
        assert(!is_happy_flag ==> !(forall|j: int| 0 < j < sl ==> three_distinct_spec(s@, j)));
    }
    is_happy_flag
}
// </vc-code>

fn main() {}
}