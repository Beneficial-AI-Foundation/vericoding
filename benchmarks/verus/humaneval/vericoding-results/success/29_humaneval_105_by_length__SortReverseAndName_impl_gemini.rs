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
fn number_to_name_exec(n: i8) -> (result: Vec<char>)
    requires
        1 <= n <= 9,
    ensures
        result@ == number_to_name(n as int),
{
    if n == 1 {
        vec!['O', 'n', 'e']
    } else if n == 2 {
        vec!['T', 'w', 'o']
    } else if n == 3 {
        vec!['T', 'h', 'r', 'e', 'e']
    } else if n == 4 {
        vec!['F', 'o', 'u', 'r']
    } else if n == 5 {
        vec!['F', 'i', 'v', 'e']
    } else if n == 6 {
        vec!['S', 'i', 'x']
    } else if n == 7 {
        vec!['S', 'e', 'v', 'e', 'n']
    } else if n == 8 {
        vec!['E', 'i', 'g', 'h', 't']
    } else {
        vec!['N', 'i', 'n', 'e']
    }
}
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
    let mut result: Vec<Vec<char>> = Vec::new();
    let mut i: usize = 0;
    while i < arr.len()
        invariant
            i <= arr.len(),
            result@.len() <= i,
            forall|j: int| 0 <= j < result@.len() ==> (
                result@[j]@ == seq!['O', 'n', 'e'] || result@[j]@ == seq!['T', 'w', 'o'] || result@[j]@ == seq!['T', 'h', 'r', 'e', 'e'] || 
                result@[j]@ == seq!['F', 'o', 'u', 'r'] || result@[j]@ == seq!['F', 'i', 'v', 'e'] || result@[j]@ == seq!['S', 'i', 'x'] || 
                result@[j]@ == seq!['S', 'e', 'v', 'e', 'n'] || result@[j]@ == seq!['E', 'i', 'g', 'h', 't'] || result@[j]@ == seq!['N', 'i', 'n', 'e']
            ),
        decreases arr.len() - i
    {
        let x = arr[i];
        if 1 <= x && x <= 9 {
            let name = number_to_name_exec(x);
            result.push(name);
        }
        i = i + 1;
    }
    result
}
// </vc-code>


}

fn main() {}