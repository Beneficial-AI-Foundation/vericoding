use vstd::prelude::*;

verus! {

// <vc-helpers>
fn pow10(exponent: nat) -> (result: nat)
    ensures result == 10_nat.pow(exponent),
{
    if exponent == 0 {
        1
    } else {
        10 * pow10((exponent - 1) as nat)
    }
}

// Function to calculate the absolute value
// TODO: find a similar function in vstd
fn abs_diff(a: int, b: int) -> (result: nat)
    ensures result == if a >= b { (a - b) as nat } else { (b - a) as nat },
{
    if a >= b { (a - b) as nat } else { (b - a) as nat }
}

// Function to calculate the product of elements in a sequence
fn prod_seq(s: Seq<int>) -> (product: int)
    ensures product == (s.len() == 0 ? 1 : s.fold_left(|acc, x| acc * x, 1)),
{
    if s.len() == 0 {
        1
    } else {
        s.fold_left(|acc, x| acc * x, 1)
    }
}
// </vc-helpers>

// <vc-spec>
fn derivative(xs: &Vec<usize>) -> (ret: Option<Vec<usize>>)
    // post-conditions-start
    ensures
        ret.is_some() ==> xs@.len() == 0 || xs@.map(|i: int, x| i * x).skip(1)
            =~= ret.unwrap()@.map_values(|x| x as int),
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    // impl-start
    if xs@.len() == 0 {
        return Some(Vec::new());
    }

    let mut result_vec: Vec<usize> = Vec::new();
    let mut i: int = 1;

    let len = xs@.len();
    while i < len
        invariant
            0 <= i <= len,
            result_vec@.len() == i - 1,
            forall|j: int| 0 <= j < i - 1 ==> #[trigger] result_vec@[j] == (j + 1) * xs@[j + 1],
    {
        let val = (i as usize) * xs@[i];
        result_vec.push(val);
        i = i + 1;
    }
    Some(result_vec)
    // impl-end
}
// </vc-code>

fn main() {}
}