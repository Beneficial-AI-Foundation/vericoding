// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
fn pad_with_zeros(s: &Vec<char>, target_len: usize, has_sign: bool) -> (result: Vec<char>)
    requires
        target_len >= s.len(),
    ensures
        result.len() == target_len,
        has_sign ==> (s.len() > 0 ==> result@[0] == s@[0]),
        has_sign ==> (s.len() > 0 ==> result@.skip(1).take((target_len - s.len()) as int) == Seq::new((target_len - s.len()) as nat, |i: int| '0')),
        has_sign ==> (s.len() > 0 ==> result@.skip((target_len - s.len() + 1) as int) == s@.skip(1)),
        !has_sign ==> (result@.take((target_len - s.len()) as int) == Seq::new((target_len - s.len()) as nat, |i: int| '0')),
        !has_sign ==> (result@.skip((target_len - s.len()) as int) == s@)
{
    let mut result = Vec::new();
    let zeros_to_add = target_len - s.len();
    
    if has_sign && s.len() > 0 {
        result.push(s[0]);
        let mut i = 0;
        while i < zeros_to_add
            invariant
                result.len() == 1 + i,
                forall|j: int| 0 <= j < result.len() ==> (j == 0 ==> result@[j] == s@[0]),
                forall|j: int| 1 <= j < result.len() ==> result@[j] == '0'
            decreases zeros_to_add - i
        {
            result.push('0');
            i += 1;
        }
        
        let mut j = 1;
        while j < s.len()
            invariant
                result.len() == 1 + zeros_to_add + (j - 1),
                forall|k: int| 0 <= k < result.len() ==> 
                    (k == 0 ==> result@[k] == s@[0]) &&
                    (1 <= k < 1 + zeros_to_add ==> result@[k] == '0') &&
                    (1 + zeros_to_add <= k < result.len() ==> result@[k] == s@[k - zeros_to_add])
            decreases s.len() - j
        {
            result.push(s[j]);
            j += 1;
        }
    } else {
        let mut i = 0;
        while i < zeros_to_add
            invariant
                result.len() == i,
                forall|j: int| 0 <= j < result.len() ==> result@[j] == '0'
            decreases zeros_to_add - i
        {
            result.push('0');
            i += 1;
        }
        
        let mut j = 0;
        while j < s.len()
            invariant
                result.len() == zeros_to_add + j,
                forall|k: int| 0 <= k < result.len() ==> 
                    (k < zeros_to_add ==> result@[k] == '0') &&
                    (zeros_to_add <= k < result.len() ==> result@[k] == s@[k - zeros_to_add])
            decreases s.len() - j
        {
            result.push(s[j]);
            j += 1;
        }
    }
    
    result
}

fn create_zeros(len: usize) -> (result: Vec<char>)
    ensures
        result.len() == len,
        all_zeros(result@)
{
    let mut result = Vec::new();
    let mut i = 0;
    while i < len
        invariant
            result.len() == i,
            all_zeros(result@)
        decreases len - i
    {
        result.push('0');
        i += 1;
    }
    result
}

/* helper modified by LLM (iteration 5): Add executable version of is_sign_char */
fn is_sign_char_exec(c: char) -> bool {
    c == '+' || c == '-'
}
// </vc-helpers>

// <vc-spec>
spec fn is_sign_char(c: char) -> bool {
    c == '+' || c == '-'
}

spec fn all_zeros(s: Seq<char>) -> bool {
    forall|i: int| 0 <= i < s.len() ==> s[i] == '0'
}

spec fn max_usize(a: usize, b: usize) -> usize {
    if a >= b { a } else { b }
}

fn zfill(a: Vec<Vec<char>>, width: usize) -> (result: Vec<Vec<char>>)
    ensures
        result.len() == a.len(),
        forall|i: int| 0 <= i < result.len() ==> 
            #[trigger] result[i].len() == max_usize(a[i].len(), width),
        forall|i: int| 0 <= i < result.len() && a[i].len() >= width ==> 
            #[trigger] result[i]@ == a[i]@,
        forall|i: int| 0 <= i < result.len() && a[i].len() < width && a[i].len() > 0 && 
            !is_sign_char(a[i]@[0]) ==> 
            #[trigger] all_zeros(result[i]@.take((width - a[i].len()) as int)) &&
            result[i]@.skip((width - a[i].len()) as int) == a[i]@,
        forall|i: int| 0 <= i < result.len() && a[i].len() < width && a[i].len() > 0 && 
            is_sign_char(a[i]@[0]) ==> 
            #[trigger] result[i]@[0] == a[i]@[0] &&
            result[i]@.skip(width as int) == a[i]@.skip(1),
        forall|i: int| 0 <= i < result.len() && a[i].len() == 0 ==> 
            #[trigger] result[i].len() == width && 
            all_zeros(result[i]@),
        forall|i: int| 0 <= i < result.len() && a[i].len() < width ==> 
            #[trigger] result[i].len() == width,
        forall|i: int| 0 <= i < result.len() && a[i].len() < width ==> 
            #[trigger] all_zeros(result[i]@.take((width - a[i].len()) as int))
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fix arithmetic underflow and invariant issues */
    let mut result: Vec<Vec<char>> = Vec::new();
    let mut i = 0;
    
    while i < a.len()
        invariant
            result.len() == i,
            forall|j: int| 0 <= j < result.len() ==> result[j].len() == max_usize(a[j].len(), width),
            forall|j: int| 0 <= j < result.len() && a[j].len() >= width ==> result[j]@ == a[j]@,
            forall|j: int| 0 <= j < result.len() && a[j].len() < width && a[j].len() > 0 && !is_sign_char(a[j]@[0]) ==> 
                all_zeros(result[j]@.take((width - a[j].len()) as int)) && 
                result[j]@.skip((width - a[j].len()) as int) == a[j]@,
            forall|j: int| 0 <= j < result.len() && a[j].len() < width && a[j].len() > 0 && is_sign_char(a[j]@[0]) ==> 
                result[j]@[0] == a[j]@[0] && 
                result[j]@.skip(1).take((width - a[j].len()) as int) == Seq::new((width - a[j].len()) as nat, |k: int| '0') &&
                result[j]@.skip((width - a[j].len() + 1) as int) == a[j]@.skip(1),
            forall|j: int| 0 <= j < result.len() && a[j].len() == 0 ==> 
                result[j].len() == width && 
                all_zeros(result[j]@),
            forall|j: int| 0 <= j < result.len() && a[j].len() < width ==> 
                result[j].len() == width,
            forall|j: int| 0 <= j < result.len() && a[j].len() < width ==> 
                all_zeros(result[j]@.take((width - a[j].len()) as int))
        decreases a.len() - i
    {
        if a[i].len() >= width {
            result.push(a[i].clone());
        } else if a[i].len() == 0 {
            result.push(create_zeros(width));
        } else {
            let has_sign = is_sign_char_exec(a[i][0]);
            result.push(pad_with_zeros(&a[i], width, has_sign));
        }
        i += 1;
    }
    
    result
}
// </vc-code>


}
fn main() {}