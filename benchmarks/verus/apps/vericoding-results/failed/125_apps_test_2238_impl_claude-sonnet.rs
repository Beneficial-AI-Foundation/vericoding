// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(n: int) -> bool {
    n >= 3 && n <= 101 && n % 2 == 1
}

spec fn valid_result(result: Seq<String>, n: int) -> bool {
    result.len() == n &&
    forall|i: int| 0 <= i < result.len() ==> #[trigger] result[i]@.len() == n
}

spec fn repeat_char(c: char, count: int) -> Seq<char>
    decreases count
{
    if count <= 0 { Seq::empty() }
    else { repeat_char(c, count - 1).push(c) }
}

spec fn correct_diamond_pattern(result: Seq<String>, n: int) -> bool {
    result.len() == n ==> {
        let magic = (n - 1) / 2;
        
        (forall|i: int| 0 <= i <= magic && i < result.len() ==> {
            let stars = magic - i;
            let diamonds = n - 2 * stars;
            #[trigger] result[i]@ == repeat_char('*', stars) + repeat_char('D', diamonds) + repeat_char('*', stars)
        }) &&
        
        (forall|i: int| magic + 1 <= i < n && i < result.len() ==> {
            let u = i - magic;
            let stars = u;
            let diamonds = n - 2 * stars;
            #[trigger] result[i]@ == repeat_char('*', stars) + repeat_char('D', diamonds) + repeat_char('*', stars)
        })
    }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed type casting and sequence indexing for Verus compatibility */
proof fn lemma_repeat_char_len(c: char, count: int)
    requires count >= 0
    ensures repeat_char(c, count).len() == count
    decreases count
{
    if count <= 0 {
    } else {
        lemma_repeat_char_len(c, count - 1);
    }
}

proof fn lemma_repeat_char_add(c1: char, c2: char, count1: int, count2: int)
    requires count1 >= 0, count2 >= 0
    ensures (repeat_char(c1, count1) + repeat_char(c2, count2)).len() == count1 + count2
{
    lemma_repeat_char_len(c1, count1);
    lemma_repeat_char_len(c2, count2);
}

proof fn lemma_seq_concatenation(s1: Seq<char>, s2: Seq<char>, s3: Seq<char>)
    ensures (s1 + s2 + s3).len() == s1.len() + s2.len() + s3.len()
{
}

fn create_string_from_spec(spec_seq: Seq<char>) -> (s: String)
    ensures s@ == spec_seq
{
    let mut result = String::new();
    let mut i: int = 0;
    while i < spec_seq.len()
        invariant
            0 <= i <= spec_seq.len(),
            result@ == spec_seq.subrange(0, i)
    {
        result.push(spec_seq@[i]);
        i += 1;
    }
    result
}
// </vc-helpers>

// <vc-spec>
fn solve(n: usize) -> (result: Vec<String>)
    requires 
        valid_input(n as int)
    ensures 
        valid_result(result@, n as int),
        correct_diamond_pattern(result@, n as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed type casting and sequence concatenation syntax */
    let mut result: Vec<String> = Vec::new();
    let magic = (n - 1) / 2;
    let mut i = 0;
    
    while i < n
        invariant
            0 <= i <= n,
            result.len() == i,
            forall|j: int| 0 <= j < i ==> #[trigger] result@[j]@.len() == n,
            forall|j: int| 0 <= j <= magic && j < i ==> {
                let stars = magic - j;
                let diamonds = n - 2 * stars;
                #[trigger] result@[j]@ == repeat_char('*', stars) + repeat_char('D', diamonds) + repeat_char('*', stars)
            },
            forall|j: int| magic + 1 <= j < n && j < i ==> {
                let u = j - magic;
                let stars = u;
                let diamonds = n - 2 * stars;
                #[trigger] result@[j]@ == repeat_char('*', stars) + repeat_char('D', diamonds) + repeat_char('*', stars)
            }
    {
        let stars: usize;
        let diamonds: usize;
        
        if i <= magic {
            stars = magic - i;
            diamonds = n - 2 * stars;
        } else {
            let u = i - magic;
            stars = u;
            diamonds = n - 2 * stars;
        }
        
        let ghost spec_stars = repeat_char('*', stars as int);
        let ghost spec_diamonds = repeat_char('D', diamonds as int);
        let ghost spec_line = spec_stars + spec_diamonds + spec_stars;
        
        proof {
            lemma_repeat_char_len('*', stars as int);
            lemma_repeat_char_len('D', diamonds as int);
            lemma_seq_concatenation(spec_stars, spec_diamonds, spec_stars);
        }
        
        let line = create_string_from_spec(spec_line);
        result.push(line);
        i += 1;
    }
    
    result
}
// </vc-code>


}

fn main() {}