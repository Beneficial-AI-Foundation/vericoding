// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn sum_prefix(ops: Seq<int>, len: nat) -> int
  recommends len <= ops.len()
  decreases len
{
  if len == 0 { 0 }
  else { sum_prefix(ops, (len - 1) as nat) + ops[len - 1] }
}

spec fn vec_to_seq_int(v: Vec<i8>) -> Seq<int> {
  v@.map(|i, x: i8| x as int)
}

  // </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn below_zero(operations: Vec<i8>) -> (result: bool)
  ensures result <==> (exists|i: int| 0 < i <= operations@.len() && #[trigger] sum_prefix(vec_to_seq_int(operations), i as nat) < 0)
// </vc-spec>
// <vc-code>
{
    let mut balance: i32 = 0;
    let mut found_negative = false;
    let mut i: usize = 0;
    
    while i < operations.len()
        invariant
            i <= operations.len(),
            balance == sum_prefix(vec_to_seq_int(operations), i as nat),
            found_negative <==> (exists|j: int| 0 < j <= i && #[trigger] sum_prefix(vec_to_seq_int(operations), j as nat) < 0),
        decreases operations.len() - i
    {
        balance = balance + operations[i] as i32;
        i = i + 1;
        
        assert(balance == sum_prefix(vec_to_seq_int(operations), i as nat));
        
        if balance < 0 {
            found_negative = true;
            assert(sum_prefix(vec_to_seq_int(operations), i as nat) < 0);
        }
    }
    
    found_negative
}
// </vc-code>


}

fn main() {}