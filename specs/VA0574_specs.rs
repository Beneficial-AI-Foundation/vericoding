// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(n: int, a: Seq<int>) -> bool {
    n >= 0 && a.len() == n && forall|i: int| 0 <= i < a.len() ==> 
        #[trigger] a[i] == 4int || #[trigger] a[i] == 8int || #[trigger] a[i] == 15int || 
        #[trigger] a[i] == 16int || #[trigger] a[i] == 23int || #[trigger] a[i] == 42int
}

spec fn number_of_complete_subsequences(n: int, a: Seq<int>) -> int {
    let k = seq![4int, 8int, 15int, 16int, 23int, 42int];
    let s = seq![n, 0int, 0int, 0int, 0int, 0int, 0int];
    let final_s = process_array(s, a, k, 0int);
    final_s[6int]
}

spec fn process_array(s: Seq<int>, a: Seq<int>, k: Seq<int>, index: int) -> Seq<int>
    decreases a.len() - index
{
    if s.len() == 7 && k.len() == 6 && 0 <= index <= a.len() &&
       (forall|i: int| 0 <= i < a.len() ==> 
            #[trigger] a[i] == 4int || #[trigger] a[i] == 8int || #[trigger] a[i] == 15int || 
            #[trigger] a[i] == 16int || #[trigger] a[i] == 23int || #[trigger] a[i] == 42int) &&
       k == seq![4int, 8int, 15int, 16int, 23int, 42int] &&
       (forall|i: int| 0 <= i < 7 ==> s[i] >= 0) {
        if index == a.len() {
            s
        } else {
            let ai = a[index];
            let new_s = update_state(s, ai, k);
            process_array(new_s, a, k, index + 1)
        }
    } else {
        seq![0int, 0int, 0int, 0int, 0int, 0int, 0int]
    }
}

spec fn update_state(s: Seq<int>, ai: int, k: Seq<int>) -> Seq<int> {
    if s.len() == 7 && k.len() == 6 &&
       (ai == 4int || ai == 8int || ai == 15int || ai == 16int || ai == 23int || ai == 42int) &&
       k == seq![4int, 8int, 15int, 16int, 23int, 42int] &&
       (forall|i: int| 0 <= i < 7 ==> s[i] >= 0) {
        if ai == k[5int] && s[5int] > 0 {
            s.update(6int, s[6int] + 1).update(5int, s[5int] - 1)
        } else if ai == k[4int] && s[4int] > 0 {
            s.update(5int, s[5int] + 1).update(4int, s[4int] - 1)
        } else if ai == k[3int] && s[3int] > 0 {
            s.update(4int, s[4int] + 1).update(3int, s[3int] - 1)
        } else if ai == k[2int] && s[2int] > 0 {
            s.update(3int, s[3int] + 1).update(2int, s[2int] - 1)
        } else if ai == k[1int] && s[1int] > 0 {
            s.update(2int, s[2int] + 1).update(1int, s[1int] - 1)
        } else if ai == k[0int] && s[0int] > 0 {
            s.update(1int, s[1int] + 1).update(0int, s[0int] - 1)
        } else {
            s
        }
    } else {
        seq![0int, 0int, 0int, 0int, 0int, 0int, 0int]
    }
}

spec fn number_of_complete_subsequences_partial(n: int, a: Seq<int>, k: Seq<int>, index: int) -> int {
    if valid_input(n, a) && k.len() == 6 && k == seq![4int, 8int, 15int, 16int, 23int, 42int] && 0 <= index <= a.len() {
        let s = seq![n, 0int, 0int, 0int, 0int, 0int, 0int];
        let partial_a = if index == 0 { seq![] } else { a.subrange(0int, index) };
        let final_s = process_array(s, partial_a, k, 0int);
        final_s[6int]
    } else {
        0int
    }
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn solve(n: i8, a: Vec<i8>) -> (result: i8)
  requires
    valid_input(n as int, a@.map(|x: i8| x as int)),
  ensures
    0 <= result as int <= n as int,
    result as int == n as int - 6 * number_of_complete_subsequences(n as int, a@.map(|x: i8| x as int)),
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>


}

fn main() {}