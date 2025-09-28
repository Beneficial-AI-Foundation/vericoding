use vstd::prelude::*;

verus! {

spec fn is_upper_case(c: char) -> bool {
    65 <= c as int <= 90
}

// <vc-helpers>
#[verifier::exec]
pub fn exec_is_upper_case(c: char) -> (result: bool)
    ensures
        result == is_upper_case(c),
{
    c >= 'A' && c <= 'Z'
}
// </vc-helpers>

// <vc-spec>
fn count_uppercase(s: &str) -> (count: usize)
    ensures 
        count >= 0,
        count as int == s@.filter(|c: char| is_upper_case(c)).len(),
// </vc-spec>
// <vc-code>
{
let mut count: usize = 0;
let mut ghost i = 0;
for mut c in s.chars() {
  proof {
      assert(s@[i] == c);
      i +=1;
  }
  if exec_is_upper_case(c) {
      count +=1;
  }
}
count
}
// </vc-code>

fn main() {}

}