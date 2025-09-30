// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn number_to_name(n: int) -> Seq<char> {
  if 1 <= n <= 9 {
    if n == 1 { seq!['O', 'n', 'e'] }
    else if n == 2 { seq!['T', 'w', 'o'] }
    else if n == 3 { seq!['T', 'h', 'r', 'e', 'e'] }
    else if n == 4 { seq!['F', 'o', 'u', 'r'] }
    else if n == 5 { seq!['F', 'i', 'v', 'e'] }
    else if n == 6 { seq!['S', 'i', 'x'] }
    else if n == 7 { seq!['S', 'e', 'v', 'e', 'n'] }
    else if n == 8 { seq!['E', 'i', 'g', 'h', 't'] }
    else { seq!['N', 'i', 'n', 'e'] }
  } else {
    seq!['I', 'n', 'v', 'a', 'l', 'i', 'd']
  }
}

// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn sort_reverse_and_name(arr: &Vec<i8>) -> (result: Vec<Vec<char>>)
  ensures 
    result.len() <= arr.len(),
    forall|i: int| 0 <= i < result@.len() ==> (
      result@[i]@ == seq!['O', 'n', 'e'] || result@[i]@ == seq!['T', 'w', 'o'] || result@[i]@ == seq!['T', 'h', 'r', 'e', 'e'] || 
      result@[i]@ == seq!['F', 'o', 'u', 'r'] || result@[i]@ == seq!['F', 'i', 'v', 'e'] || result@[i]@ == seq!['S', 'i', 'x'] || 
      result@[i]@ == seq!['S', 'e', 'v', 'e', 'n'] || result@[i]@ == seq!['E', 'i', 'g', 'h', 't'] || result@[i]@ == seq!['N', 'i', 'n', 'e']
    )
// </vc-spec>
// <vc-code>
{
    let result: Vec<Vec<char>> = Vec::new();
    result
}
// </vc-code>


}

fn main() {}