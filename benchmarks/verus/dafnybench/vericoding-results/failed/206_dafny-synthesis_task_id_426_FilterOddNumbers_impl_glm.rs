use vstd::prelude::*;

verus! {

/**
 * Filter odd numbers from an array of numbers
 **/

spec fn is_odd(n: int) -> bool {
    n % 2 != 0
}

// <vc-helpers>
proof fn is_odd_def(n: int)
    ensures is_odd(n) <==> (n % 2 != 0)
{
}

fn lemma_mod_int(n: int, d: int)
    requires d != 0
    ensures (n % d) is int,
{
    // Built-in property in Verus
}

proof fn lemma_is_odd_rem(n: int)
    ensures is_odd(n) <==> (n % 2 != 0)
{
    // This lemma relates the int-based modulo operation to the is_odd spec function
    // Since n is int and 2 is int, n % 2 is valid in ghost code
    if n % 2 != 0 {
        assert(is_odd(n));
    } else {
        assert(!is_odd(n));
    }
}
// </vc-helpers>

// <vc-spec>
fn filter_odd_numbers(arr: &[int]) -> (odd_list: Vec<int>)
    ensures 
        // All numbers in the output are odd and exist in the input 
        forall|i: int| 0 <= i < odd_list.len() ==> is_odd(odd_list[i]) && arr@.contains(odd_list[i]),
        // All odd numbers in the input are in the output
        forall|i: int| 0 <= i < arr.len() && is_odd(arr[i]) ==> odd_list@.contains(arr[i]),
// </vc-spec>
// <vc-code>
{
    let mut result = Vec::new();
    for i in 0..arr.len()
        invariant
            forall|k: int| 0 <= k < result.len() ==> is_odd(result@[k]) && arr@.contains(result@[k]),
            forall|j: int| 0 <= j < i && is_odd(arr[j]) ==> result@.contains(arr[j])
    {
        let elem = arr[i];
        proof {
            lemma_mod_int(elem, 2);
            lemma_is_odd_rem(elem);
        }
        if is_odd(elem) {
            result.push(elem);
        }
    }
    result
}
// </vc-code>

fn main() {}

}