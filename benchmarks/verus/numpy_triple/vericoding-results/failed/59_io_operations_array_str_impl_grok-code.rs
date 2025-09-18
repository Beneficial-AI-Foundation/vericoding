// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
proof fn concat_preserves_first(prefix: Seq<char>, suffix: Seq<char>)
    requires prefix.len() > 0
    ensures (prefix + suffix)[0 as int] == prefix[0 as int]
{
}

proof fn concat_preserves_last(prefix: Seq<char>, suffix: Seq<char>)
    requires suffix.len() > 0
    ensures (prefix + suffix)[((prefix + suffix).len() - 1) as int] == suffix[(suffix.len() - 1) as int]
{
}

/* helper modified by LLM (iteration 5): added proofs to preserve first and last characters in string concatenation */
// </vc-helpers>

// <vc-spec>
fn array_str(a: Vec<f32>) -> (result: String)
    ensures 
        result@.len() > 0,
        a.len() == 0 ==> result@ == "[]"@,
        a.len() > 0 ==> result@[0] == '[' && result@[(result@.len() - 1) as int] == ']',
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): implemented using string concatenation instead of push_str to avoid compilation error */
    if a.len() == 0 {
        "[]".to_string()
    } else {
        let mut result = "[".to_string() + &a[0].to_string();
        let mut i = 1usize;
        while i < a.len()
            invariant
                i >= 1,
                i <= a.len(),
                a.len() > 0,
                result@.len() > 0,
                result@[0 as int] == '['
        {
            proof {
                // proof steps if needed
            }
            result = result + ", " + &a[i].to_string();
            i = i + 1;
        }
        result = result + "]";
        result
    }
}
// </vc-code>

}
fn main() {}