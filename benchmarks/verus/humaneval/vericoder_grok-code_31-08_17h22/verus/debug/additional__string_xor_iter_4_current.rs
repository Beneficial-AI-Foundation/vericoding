use vstd::prelude::*;

verus! {

// <vc-helpers>
// Empty as no additional helpers needed.
// </vc-helpers>

// <vc-spec>
#[verifier::loop_isolation(false)]
fn string_xor(a: &[char], b: &[char]) -> (result: Vec<char>)
    // pre-conditions-start
    requires
        a.len() == b.len(),
        forall|i: int| 0 <= i && i < a.len() ==> a[i] == '0' || a[i] == '1',
        forall|i: int| 0 <= i && i < b.len() ==> b[i] == '0' || b[i] == '1',
    // pre-conditions-end
    // post-conditions-start
    ensures
        result.len() == a.len(),
        forall|i: int| 0 <= i && i < result.len() ==> (result[i] == '0' || result[i] == '1'),
        forall|i: int| 0 <= i && i < result.len() ==> result[i] == (if a[i] == b[i] { '0' } else { '1' })
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    let mut result: Vec<char> = Vec::new();
    for i in 0..a.len()
        invariant
        result.len() == i,
        i <= a.len(),
        forall |k: int| 0 <= k && k < i ==> #[trigger] result@[k] == (if a@[k] == b@[k] { '0' } else { '1' }),
        forall |k: int| 0 <= k && k < i ==> result@[k] == '0' || result@[k] == '1',
    {
        proof {
            let k = i as int;
            assert(xor_char == if a@[k] == b@[k] { '0' } else { '1' });    // xor_char not defined yet, move below
        }
        let a_char = a[i];
        let b_char = b[i];
        let xor_char = if a_char == b_char { '0' } else { '1' };
        proof {
            let k = i as int;
            assert(xor_char == if a@[k] == b@[k] { '0' } else { '1' });
            assert(xor_char == '0' || xor_char == '1');
        }
        result.push(xor_char);
    }
    result
}
// </vc-code>

fn main() {}
}