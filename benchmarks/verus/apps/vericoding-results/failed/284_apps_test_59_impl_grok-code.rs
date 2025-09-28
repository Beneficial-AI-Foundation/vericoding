// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(n: int, a: Seq<int>, p: Seq<char>) -> bool {
    n >= 2 &&
    a.len() == n &&
    p.len() == n - 1 &&
    (forall|i: int| 0 <= i < p.len() ==> #[trigger] p[i] == '0' || #[trigger] p[i] == '1') &&
    (forall|i: int| 0 <= i < a.len() ==> 1 <= #[trigger] a[i] <= n) &&
    a.to_set() =~= Set::new(|i: int| 1 <= i <= n)
}

spec fn max_up_to(a: Seq<int>, i: int) -> int
    recommends 0 <= i < a.len()
    decreases i when i >= 0
{
    if i == 0 { 
        a[0] 
    } else if i > 0 && a[i] > max_up_to(a, i-1) { 
        a[i] 
    } else if i > 0 { 
        max_up_to(a, i-1) 
    } else {
        a[0]
    }
}

spec fn can_sort(n: int, a: Seq<int>, p: Seq<char>) -> bool
    recommends valid_input(n, a, p)
{
    forall|i: int| 0 <= i < n - 1 ==> 
        (#[trigger] p[i] == '0' ==> max_up_to(a, i) <= i + 1)
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Added string_new and string_append_char helper functions for string construction */fn string_new() -> String {
    String::new()
}

fn string_append_char(mut s: String, c: char) -> String {
    s.push(c);
    s
}
// </vc-helpers>

// <vc-spec>
fn solve(n: i8, a: Vec<i8>, p: Vec<char>) -> (result: String)
    requires
        valid_input(n as int, a@.map(|i, x| x as int), p@),
    ensures
        result@ == seq!['Y', 'E', 'S'] || result@ == seq!['N', 'O'],
        (result@ == seq!['Y', 'E', 'S']) <==> can_sort(n as int, a@.map(|i, x| x as int), p@),
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Replace string operations with calls to helper functions */{
    let mut answer = true;
    let mut max_so_far: i8 = a[0];
    proof {
        assert(max_so_far as int == a@[0 as int]);
        assert(max_so_far as int == max_up_to(a@.map(|j, x| x as int), 0));
    }
    for i in 0..(n as usize - 1) {
        let i_usize = i;
        proof {
            assert(i_usize as int == i as int);
        }
        if p[i] == '0' && max_so_far > (i as i8 + 1) {
            answer = false;
        }
        let next_val: i8 = a[i + 1];
        if next_val > max_so_far {
            max_so_far = next_val;
        }
        proof {
            assert(max_so_far as int >= a@[(i as int) + 1]);
            assert(max_so_far as int == max_up_to(a@.map(|j, x| x as int), (i as int) + 1));
        }
    }
    if answer {
        string_append_char(string_append_char(string_append_char(string_new(), 'Y'), 'E'), 'S')
    } else {
        string_append_char(string_append_char(string_new(), 'N'), 'O')
    }
}
// </vc-code>


}

fn main() {}