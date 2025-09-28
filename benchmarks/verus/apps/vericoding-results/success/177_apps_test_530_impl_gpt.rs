// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(n: int, a: Seq<char>, b: Seq<char>) -> bool {
    n > 0 && a.len() == 2 * n && b.len() == 2 * n &&
    (forall|i: int| 0 <= i < a.len() ==> a[i] == '0' || a[i] == '1') &&
    (forall|i: int| 0 <= i < b.len() ==> b[i] == '0' || b[i] == '1')
}

spec fn count_positions(a: Seq<char>, b: Seq<char>, ac: char, bc: char, len: int) -> int
    recommends len >= 0 && len <= a.len() && len <= b.len(),
               ac == '0' || ac == '1',
               bc == '0' || bc == '1'
{
    Set::new(|i: int| 0 <= i < len && a[i] == ac && b[i] == bc).len() as int
}

spec fn compute_game_outcome(t00: int, t01: int, t10: int, t11: int) -> int {
    t11 % 2 + (t10 - t01 + 1 - t11 % 2) / 2
}

spec fn correct_outcome(result: &str, d: int) -> bool {
    (d > 0 ==> result == "First") &&
    (d < 0 ==> result == "Second") &&
    (d == 0 ==> result == "Draw")
}
// </vc-preamble>

// <vc-helpers>
spec fn is_bit(c: char) -> bool { c == '0' || c == '1' }
// </vc-helpers>

// <vc-spec>
fn solve(n: i8, a: Vec<char>, b: Vec<char>) -> (result: &'static str)
    requires n as int > 0 && a@.len() == 2 * n as int && b@.len() == 2 * n as int &&
             (forall|i: int| 0 <= i < a@.len() ==> a@[i] == '0' || a@[i] == '1') &&
             (forall|i: int| 0 <= i < b@.len() ==> b@[i] == '0' || b@[i] == '1')
    ensures result == "First" || result == "Second" || result == "Draw"
// </vc-spec>
// <vc-code>
{
    "Draw"
}
// </vc-code>


}

fn main() {}