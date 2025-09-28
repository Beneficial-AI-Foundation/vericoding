// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

proof fn lemma_max_usize_commutative(a: usize, b: usize)
    ensures
        max_usize(a, b) == max_usize(b, a),
{
}

proof fn lemma_max_usize_ge_both(a: usize, b: usize)
    ensures
        max_usize(a, b) >= a,
        max_usize(a, b) >= b,
{
}

proof fn lemma_all_zeros_append(s1: Seq<char>, s2: Seq<char>)
    requires
        all_zeros(s1),
        all_zeros(s2),
    ensures
        all_zeros(s1 + s2),
{
}

proof fn lemma_all_zeros_take_skip(s: Seq<char>, n: int)
    requires
        all_zeros(s),
        0 <= n <= s.len(),
    ensures
        all_zeros(s.take(n)),
        all_zeros(s.skip(n)),
{
}

proof fn lemma_seq_skip_take_identity(s: Seq<char>, n: int)
    requires
        0 <= n <= s.len(),
    ensures
        s.take(n) + s.skip(n) == s,
{
}

proof fn lemma_seq_take_skip_append(s: Seq<char>, n: int)
    requires
        0 <= n <= s.len(),
    ensures
        s == s.take(n) + s.skip(n),
{
}

proof fn lemma_seq_skip_skip(s: Seq<char>, n: int, m: int)
    requires
        0 <= n <= m <= s.len(),
    ensures
        s.skip(n).skip(m - n) == s.skip(m),
{
}

proof fn lemma_seq_take_take(s: Seq<char>, n: int, m: int)
    requires
        0 <= n <= m <= s.len(),
    ensures
        s.take(n).take(m) == s.take(n),
{
}

/* helper modified by LLM (iteration 5): fix seq_index parameter types to use usize */
spec fn seq_index<T>(s: Seq<T>, i: usize) -> T {
    s[i as int]
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
    /* code modified by LLM (iteration 5): fix integer conversions for seq_index calls */
    let mut result: Vec<Vec<char>> = Vec::new();
    let mut i: usize = 0;
    
    while i < a.len()
        invariant
            result.len() == i,
            forall|j: int| 0 <= j < i ==> #[trigger] result[j].len() == max_usize(a[j].len(), width),
            forall|j: int| 0 <= j < i && a[j].len() >= width ==> #[trigger] result[j]@ == a[j]@,
            forall|j: int| 0 <= j < i && a[j].len() < width && a[j].len() > 0 && !is_sign_char(seq_index(a[j]@, 0)) ==> 
                #[trigger] all_zeros(result[j]@.take((width - a[j].len()) as int)) && 
                result[j]@.skip((width - a[j].len()) as int) == a[j]@,
            forall|j: int| 0 <= j < i && a[j].len() < width && a[j].len() > 0 && is_sign_char(seq_index(a[j]@, 0)) ==> 
                #[trigger] result[j]@[0] == seq_index(a[j]@, 0) && 
                result[j]@.skip(width as int) == a[j]@.skip(1),
            forall|j: int| 0 <= j < i && a[j].len() == 0 ==> 
                #[trigger] result[j].len() == width && 
                all_zeros(result[j]@),
            forall|j: int| 0 <= j < i && a[j].len() < width ==> 
                #[trigger] result[j].len() == width,
            forall|j: int| 0 <= j < i && a[j].len() < width ==> 
                #[trigger] all_zeros(result[j]@.take((width - a[j].len()) as int)),
        decreases a.len() - i,
    {
        let original = &a[i];
        let orig_seq = original@;  // Extract sequence for indexing
        let mut padded = Vec::new();
        
        if original.len() >= width {
            padded = original.clone();
        } else if original.len() == 0 {
            let mut j: usize = 0;
            while j < width
                invariant
                    padded.len() == j,
                    forall|k: int| 0 <= k < j ==> padded@[k] == '0',
                decreases width - j,
            {
                padded.push('0');
                j += 1;
            }
        } else if is_sign_char(seq_index(orig_seq, 0)) {
            padded.push(seq_index(orig_seq, 0));
            let mut j: usize = 0;
            while j < width - original.len()
                invariant
                    padded.len() == 1 + j,
                    padded@[0] == seq_index(orig_seq, 0),
                    forall|k: int| 1 <= k < 1 + j ==> padded@[k] == '0',
                decreases width - original.len() - j,
            {
                padded.push('0');
                j += 1;
            }
            let mut k: usize = 1;
            while k < original.len()
                invariant
                    padded.len() == width - original.len() + 1 + (k - 1),
                    padded@[0] == seq_index(orig_seq, 0),
                    forall|m: int| 1 <= m < width - original.len() + 1 ==> padded@[m] == '0',
                    forall|m: int| width - original.len() + 1 <= m < padded.len() ==> 
                        padded@[m] == seq_index(orig_seq, (m - (width - original.len())) as usize),
                decreases original.len() - k,
            {
                padded.push(seq_index(orig_seq, k));
                k += 1;
            }
        } else {
            let mut j: usize = 0;
            while j < width - original.len()
                invariant
                    padded.len() == j,
                    forall|k: int| 0 <= k < j ==> padded@[k] == '0',
                decreases width - original.len() - j,
            {
                padded.push('0');
                j += 1;
            }
            let mut k: usize = 0;
            while k < original.len()
                invariant
                    padded.len() == width - original.len() + k,
                    forall|m: int| 0 <= m < width - original.len() ==> padded@[m] == '0',
                    forall|m: int| width - original.len() <= m < width - original.len() + k ==> 
                        padded@[m] == seq_index(orig_seq, (m - (width - original.len())) as usize),
                decreases original.len() - k,
            {
                padded.push(seq_index(orig_seq, k));
                k += 1;
            }
        }
        
        result.push(padded);
        i += 1;
    }
    
    result
}
// </vc-code>


}
fn main() {}