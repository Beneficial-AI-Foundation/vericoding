// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(n: int) -> bool {
    n >= 3 && n <= 101 && n % 2 == 1
}

spec fn valid_result(result: Seq<String>, n: int) -> bool {
    result.len() == n &&
    forall|i: int| 0 <= i < result.len() ==> #[trigger] result[i]@.len() == n
}

spec fn repeat_char(c: char, count: int) -> Seq<char>
    decreases count
{
    if count <= 0 { Seq::empty() }
    else { repeat_char(c, count - 1).push(c) }
}

spec fn correct_diamond_pattern(result: Seq<String>, n: int) -> bool {
    result.len() == n ==> {
        let magic = (n - 1) / 2;
        
        (forall|i: int| 0 <= i <= magic && i < result.len() ==> {
            let stars = magic - i;
            let diamonds = n - 2 * stars;
            #[trigger] result[i]@ == repeat_char('*', stars) + repeat_char('D', diamonds) + repeat_char('*', stars)
        }) &&
        
        (forall|i: int| magic + 1 <= i < n && i < result.len() ==> {
            let u = i - magic;
            let stars = u;
            let diamonds = n - 2 * stars;
            #[trigger] result[i]@ == repeat_char('*', stars) + repeat_char('D', diamonds) + repeat_char('*', stars)
        })
    }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): make_line_string builds a runtime String for a diamond line */
fn make_line_string(stars: usize, diamonds: usize) -> String {
    let mut s = std::string::String::new();
    let mut i: usize = 0;
    while i < stars
        invariant
            i <= stars,
        decreases stars - i
    {
        s.push('*');
        i += 1;
    }

    let mut j: usize = 0;
    while j < diamonds
        invariant
            j <= diamonds,
        decreases diamonds - j
    {
        s.push('D');
        j += 1;
    }

    let mut k: usize = 0;
    while k < stars
        invariant
            k <= stars,
        decreases stars - k
    {
        s.push('*');
        k += 1;
    }

    s
}
// </vc-helpers>

// <vc-spec>
fn solve(n: usize) -> (result: Vec<String>)
    requires 
        valid_input(n as int)
    ensures 
        valid_result(result@, n as int),
        correct_diamond_pattern(result@, n as int)
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 5): implement solve using runtime helper make_line_string */
  let magic: usize = (n - 1) / 2;

  let mut res: Vec<String> = Vec::new();

  let mut i: usize = 0;
  while i < n
      invariant
          i <= n,
          res.len() == i,
      decreases n - i
  {
      let idx = i;
      let stars = if idx <= magic { magic - idx } else { idx - magic };
      let diamonds = n - 2 * stars;

      let line: String = make_line_string(stars, diamonds);
      res.push(line);
      i += 1;
  }

  res
}
// </vc-code>


}

fn main() {}