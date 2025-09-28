// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn transform_element(x: int) -> int {
    if x % 2 == 0 { x - 1 } else { x }
}

spec fn valid_transformation(input: Seq<int>, output: Seq<int>) -> bool {
    output.len() == input.len() &&
    forall|i: int| 0 <= i < input.len() ==> output[i] == transform_element(input[i])
}
// </vc-preamble>

// <vc-helpers>
lemma seq_map_len<T, U>(s: Seq<T>, f: spec_fn(int, T) -> U)
    ensures s.map(f).len() == s.len()
{
}

lemma seq_map_index<T, U>(s: Seq<T>, f: spec_fn(int, T) -> U, i: int)
    requires 0 <= i < s.len()
    ensures s.map(f)[i] == f(i, s[i])
{
}
// </vc-helpers>

// <vc-spec>
fn solve(a: Vec<i8>) -> (result: Vec<i8>)
    ensures valid_transformation(a@.map(|_i, x| x as int), result@.map(|_i, x| x as int))
// </vc-spec>
// <vc-code>
{
    let mut result = Vec::new();
    let mut idx = 0;
    
    while idx < a.len()
        invariant
            0 <= idx <= a.len(),
            result.len() == idx,
            forall|i: int| 0 <= i < idx ==> result@[i] == transform_element(a@[i] as int) as i8,
        decreases a.len() - idx
    {
        let val = a[idx] as int;
        let transformed = if val % 2 == 0 { val - 1 } else { val };
        result.push(transformed as i8);
        idx += 1;
    }
    
    proof {
        seq_map_len(a@, |_i, x| x as int);
        seq_map_len(result@, |_i, x| x as int);
        
        assert(result@.map(|_i, x| x as int).len() == result.len());
        assert(a@.map(|_i, x| x as int).len() == a.len());
        assert(result.len() == a.len());
        
        assert(forall|i: int| 0 <= i < a@.map(|_i, x| x as int).len() ==> {
            seq_map_index(a@, |_i, x| x as int, i);
            seq_map_index(result@, |_i, x| x as int, i);
            result@.map(|_i, x| x as int)[i] == transform_element(a@.map(|_i, x| x as int)[i])
        });
    }
    
    result
}
// </vc-code>


}

fn main() {}