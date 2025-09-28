// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
proof fn lemma_all_zeros_take(s: Seq<char>, n: int)
    requires
        n >= 0,
        n <= s.len(),
        all_zeros(s),
    ensures
        all_zeros(s.take(n)),
{
}

proof fn lemma_all_zeros_skip(s: Seq<char>, n: int)
    requires
        n >= 0,
        n <= s.len(),
        all_zeros(s),
    ensures
        all_zeros(s.skip(n)),
{
}

/* helper modified by LLM (iteration 5): fixed postcondition to properly ensure count length */
fn create_zeros(count: usize) -> (result: Vec<char>)
    ensures
        result.len() == count,
        all_zeros(result@),
{
    let mut zeros = Vec::new();
    let mut i = 0;
    while i < count
        invariant
            i <= count,
            zeros.len() == i,
            all_zeros(zeros@),
        decreases count - i
    {
        zeros.push('0');
        i += 1;
    }
    zeros
}

exec fn is_sign_char_exec(c: char) -> (result: bool)
    ensures
        result == is_sign_char(c),
{
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
    /* code modified by LLM (iteration 5): fixed loop invariants and ensured proper sequence construction with correct bounds */
    let mut result: Vec<Vec<char>> = Vec::new();
    let mut i = 0;
    
    while i < a.len()
        invariant
            i <= a.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> 
                #[trigger] result[j].len() == max_usize(a[j].len(), width),
            forall|j: int| 0 <= j < i && a[j].len() >= width ==> 
                #[trigger] result[j]@ == a[j]@,
            forall|j: int| 0 <= j < i && a[j].len() < width && a[j].len() > 0 && 
                !is_sign_char(a[j]@[0]) ==> 
                #[trigger] all_zeros(result[j]@.take((width - a[j].len()) as int)) &&
                result[j]@.skip((width - a[j].len()) as int) == a[j]@,
            forall|j: int| 0 <= j < i && a[j].len() < width && a[j].len() > 0 && 
                is_sign_char(a[j]@[0]) ==> 
                #[trigger] result[j]@[0] == a[j]@[0] &&
                all_zeros(result[j]@.skip(1).take((width - a[j].len()) as int)) &&
                result[j]@.skip(1 + (width - a[j].len()) as int) == a[j]@.skip(1),
            forall|j: int| 0 <= j < i && a[j].len() == 0 ==> 
                #[trigger] result[j].len() == width && 
                all_zeros(result[j]@),
        decreases a.len() - i
    {
        let current = &a[i];
        
        if current.len() >= width {
            result.push(current.clone());
        } else if current.len() == 0 {
            let zeros = create_zeros(width);
            result.push(zeros);
        } else if current.len() > 0 && is_sign_char_exec(current[0]) {
            let mut new_string = Vec::new();
            new_string.push(current[0]);
            
            let zeros_needed = width - current.len();
            let mut j = 0;
            while j < zeros_needed
                invariant
                    j <= zeros_needed,
                    new_string.len() == 1 + j,
                    j < zeros_needed ==> new_string@[0] == current[0],
                    all_zeros(new_string@.skip(1).take(j as int)),
                decreases zeros_needed - j
            {
                new_string.push('0');
                j += 1;
            }
            
            let mut k = 1;
            while k < current.len()
                invariant
                    k <= current.len(),
                    1 <= k,
                    new_string.len() == zeros_needed + k,
                    new_string@[0] == current[0],
                    all_zeros(new_string@.skip(1).take(zeros_needed as int)),
                    new_string@.skip(1 + zeros_needed as int).take((k - 1) as int) == current@.skip(1).take((k - 1) as int),
                decreases current.len() - k
            {
                new_string.push(current[k]);
                k += 1;
            }
            
            result.push(new_string);
        } else {
            let zeros_needed = width - current.len();
            let zeros = create_zeros(zeros_needed);
            
            let mut new_string = zeros;
            let mut j = 0;
            while j < current.len()
                invariant
                    j <= current.len(),
                    new_string.len() == zeros_needed + j,
                    all_zeros(new_string@.take(zeros_needed as int)),
                    new_string@.skip(zeros_needed as int).take(j as int) == current@.take(j as int),
                decreases current.len() - j
            {
                new_string.push(current[j]);
                j += 1;
            }
            
            result.push(new_string);
        }
        
        i += 1;
    }
    
    result
}
// </vc-code>


}
fn main() {}