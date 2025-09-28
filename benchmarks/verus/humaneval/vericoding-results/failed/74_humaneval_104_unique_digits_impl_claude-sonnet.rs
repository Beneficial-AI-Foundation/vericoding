// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn has_no_even_digit(n: int) -> bool
  decreases n
{
  n >= 0 && ((n < 10 && n % 2 == 1) || (n % 2 == 1 && has_no_even_digit(n / 10)))
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed loop invariant and logic for has_no_even_digit_exec */
fn has_no_even_digit_exec(n: u8) -> (result: bool)
    ensures result == has_no_even_digit(n as int)
{
    let mut num = n;
    while num > 0
        invariant
            has_no_even_digit(n as int) == has_no_even_digit(num as int),
        decreases num
    {
        if num % 2 == 0 {
            return false;
        }
        num = num / 10;
    }
    true
}

fn contains_exec(v: &Vec<u8>, elem: u8) -> (result: bool)
    ensures result == v@.contains(elem)
{
    for i in 0..v.len()
        invariant
            !v@.subrange(0, i as int).contains(elem),
    {
        if v[i] == elem {
            return true;
        }
    }
    false
}
// </vc-helpers>

// <vc-spec>
fn unique_digits(x: Vec<u8>) -> (result: Vec<u8>)
  ensures 
    forall|i: int| 0 <= i < result@.len() ==> has_no_even_digit(result@[i] as int) &&
    forall|i: int, j: int| 0 <= i < j < result@.len() ==> result@[i] <= result@[j] &&
    forall|e: u8| x@.contains(e) && has_no_even_digit(e as int) ==> result@.contains(e) &&
    forall|e: u8| result@.contains(e) ==> x@.contains(e)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): simplified to use Vec methods correctly */
    let mut filtered = Vec::new();
    
    for i in 0..x.len()
        invariant
            filtered@.len() <= i,
            forall|e: u8| filtered@.contains(e) ==> x@.contains(e) && has_no_even_digit(e as int),
            forall|e: u8| x@.subrange(0, i as int).contains(e) && has_no_even_digit(e as int) ==> filtered@.contains(e),
    {
        let digit = x[i];
        if has_no_even_digit_exec(digit) {
            if !contains_exec(&filtered, digit) {
                filtered.push(digit);
            }
        }
    }
    
    // Sort the filtered vector using simple bubble sort
    let mut result = filtered;
    let len = result.len();
    
    for i in 0..len
        invariant
            result@.len() == len,
            forall|e: u8| result@.contains(e) ==> x@.contains(e) && has_no_even_digit(e as int),
            forall|e: u8| x@.contains(e) && has_no_even_digit(e as int) ==> result@.contains(e),
            forall|a: int, b: int| 0 <= a < b < i ==> result@[a] <= result@[b],
    {
        for j in (i + 1)..len
            invariant
                result@.len() == len,
                forall|e: u8| result@.contains(e) ==> x@.contains(e) && has_no_even_digit(e as int),
                forall|e: u8| x@.contains(e) && has_no_even_digit(e as int) ==> result@.contains(e),
                forall|a: int, b: int| 0 <= a < b < i ==> result@[a] <= result@[b],
                forall|k: int| (i + 1) as int <= k < j ==> result@[i as int] <= result@[k],
                i < result@.len(),
                j < result@.len(),
        {
            if result[i] > result[j] {
                let temp = result[i];
                result.set(i, result[j]);
                result.set(j, temp);
            }
        }
    }
    
    result
}
// </vc-code>


}

fn main() {}