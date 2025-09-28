// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): added decreases clauses to all while loops */
fn is_sign_char_exec(c: char) -> (result: bool)
    ensures
        result == is_sign_char(c),
{
    c == '+' || c == '-'
}

fn zero_fill_string(s: &Vec<char>, width: usize) -> (result: Vec<char>)
    requires
        width >= s.len(),
    ensures
        result.len() == width,
        s.len() > 0 && !is_sign_char(s@[0]) ==> 
            all_zeros(result@.take((width - s.len()) as int)) &&
            result@.skip((width - s.len()) as int) == s@,
        s.len() > 0 && is_sign_char(s@[0]) ==> 
            result@[0] == s@[0] &&
            all_zeros(result@.skip(1).take((width - s.len()) as int)) &&
            result@.skip((width - s.len() + 1) as int) == s@.skip(1),
        s.len() == 0 ==> all_zeros(result@),
{
    let mut result = Vec::new();
    
    if s.len() == 0 {
        let mut i: usize = 0;
        while i < width
            invariant
                i <= width,
                result.len() == i,
                all_zeros(result@),
            decreases width - i
        {
            result.push('0');
            i = i + 1;
        }
    } else if is_sign_char_exec(s[0]) {
        result.push(s[0]);
        
        let zeros_needed = width - s.len();
        let mut i: usize = 0;
        while i < zeros_needed
            invariant
                i <= zeros_needed,
                result.len() == i + 1,
                result@[0] == s@[0],
                all_zeros(result@.skip(1)),
            decreases zeros_needed - i
        {
            result.push('0');
            i = i + 1;
        }
        
        let mut j: usize = 1;
        while j < s.len()
            invariant
                1 <= j <= s.len(),
                result.len() == zeros_needed + j,
                result@[0] == s@[0],
                all_zeros(result@.skip(1).take(zeros_needed as int)),
                result@.skip((zeros_needed + 1) as int) == s@.skip(1).take((j - 1) as int),
            decreases s.len() - j
        {
            result.push(s[j]);
            j = j + 1;
        }
    } else {
        let zeros_needed = width - s.len();
        let mut i: usize = 0;
        while i < zeros_needed
            invariant
                i <= zeros_needed,
                result.len() == i,
                all_zeros(result@),
            decreases zeros_needed - i
        {
            result.push('0');
            i = i + 1;
        }
        
        let mut j: usize = 0;
        while j < s.len()
            invariant
                j <= s.len(),
                result.len() == zeros_needed + j,
                all_zeros(result@.take(zeros_needed as int)),
                result@.skip(zeros_needed as int) == s@.take(j as int),
            decreases s.len() - j
        {
            result.push(s[j]);
            j = j + 1;
        }
    }
    
    result
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
    /* code modified by LLM (iteration 4): added decreases clause to main loop */
    let mut result: Vec<Vec<char>> = Vec::new();
    let mut i: usize = 0;
    
    while i < a.len()
        invariant
            i <= a.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> #[trigger] result[j].len() == max_usize(a[j].len(), width),
            forall|j: int| 0 <= j < i && a[j].len() >= width ==> #[trigger] result[j]@ == a[j]@,
            forall|j: int| 0 <= j < i && a[j].len() < width && a[j].len() > 0 && 
                !is_sign_char(a[j]@[0]) ==> 
                #[trigger] all_zeros(result[j]@.take((width - a[j].len()) as int)) &&
                result[j]@.skip((width - a[j].len()) as int) == a[j]@,
            forall|j: int| 0 <= j < i && a[j].len() < width && a[j].len() > 0 && 
                is_sign_char(a[j]@[0]) ==> 
                #[trigger] result[j]@[0] == a[j]@[0] &&
                result[j]@.skip(width as int) == a[j]@.skip(1),
            forall|j: int| 0 <= j < i && a[j].len() == 0 ==> 
                #[trigger] result[j].len() == width && all_zeros(result[j]@),
            forall|j: int| 0 <= j < i && a[j].len() < width ==> 
                #[trigger] result[j].len() == width,
            forall|j: int| 0 <= j < i && a[j].len() < width ==> 
                #[trigger] all_zeros(result[j]@.take((width - a[j].len()) as int)),
        decreases a.len() - i
    {
        let current = &a[i];
        
        if current.len() >= width {
            result.push(current.clone());
        } else {
            let filled = zero_fill_string(current, width);
            result.push(filled);
        }
        
        i = i + 1;
    }
    
    result
}
// </vc-code>


}
fn main() {}