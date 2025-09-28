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
/* helper modified by LLM (iteration 5): Using vec of chars to build string */
fn create_line(stars: usize, diamonds: usize) -> (result: String)
    requires
        stars + diamonds + stars <= usize::MAX
    ensures
        result@.len() == stars + diamonds + stars,
        result@ == repeat_char('*', stars as int) + repeat_char('D', diamonds as int) + repeat_char('*', stars as int)
{
    let total_len = stars + diamonds + stars;
    let mut chars: Vec<char> = Vec::with_capacity(total_len);
    
    let mut i = 0;
    while i < stars
        invariant
            i <= stars,
            chars.len() == i,
            forall|j: int| 0 <= j < i ==> chars@[j] == '*'
    {
        chars.push('*');
        i += 1;
    }
    
    i = 0;
    while i < diamonds
        invariant
            i <= diamonds,
            chars.len() == stars + i,
            forall|j: int| 0 <= j < stars ==> chars@[j] == '*',
            forall|j: int| stars <= j < stars + i ==> chars@[j] == 'D'
    {
        chars.push('D');
        i += 1;
    }
    
    i = 0;
    while i < stars
        invariant
            i <= stars,
            chars.len() == stars + diamonds + i,
            forall|j: int| 0 <= j < stars ==> chars@[j] == '*',
            forall|j: int| stars <= j < stars + diamonds ==> chars@[j] == 'D',
            forall|j: int| stars + diamonds <= j < stars + diamonds + i ==> chars@[j] == '*'
    {
        chars.push('*');
        i += 1;
    }
    
    // Convert Vec<char> to String
    let mut result = String::with_capacity(total_len);
    let mut i = 0;
    while i < chars.len()
        invariant
            i <= chars.len(),
            result@.len() == i,
            forall|j: int| 0 <= j < i ==> result@[j] == chars@[j]
    {
        result.push(chars[i]);
        i += 1;
    }
    
    assert(result@.len() == total_len);
    assert(forall|j: int| 0 <= j < stars ==> result@[j] == '*');
    assert(forall|j: int| stars <= j < stars + diamonds ==> result@[j] == 'D');
    assert(forall|j: int| stars + diamonds <= j < total_len ==> result@[j] == '*');
    
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
    /* code modified by LLM (iteration 5): No changes needed in main code */
    let magic = (n - 1) / 2;
    let mut result: Vec<String> = Vec::new();
    let mut i: usize = 0;
    
    while i <= magic
        invariant
            n >= 3,
            n <= 101,
            n % 2 == 1,
            magic == (n - 1) / 2,
            i <= magic + 1,
            result.len() == i,
            forall|j: int| 0 <= j < i ==> #[trigger] result@[j]@.len() == n,
            forall|j: int| 0 <= j < i ==> {
                let stars = magic - j;
                let diamonds = n - 2 * stars;
                #[trigger] result@[j]@ == repeat_char('*', stars as int) + repeat_char('D', diamonds as int) + repeat_char('*', stars as int)
            }
    {
        let stars = magic - i;
        let diamonds = n - 2 * stars;
        let line = create_line(stars, diamonds);
        result.push(line);
        i += 1;
    }
    
    while i < n
        invariant
            n >= 3,
            n <= 101,
            n % 2 == 1,
            magic == (n - 1) / 2,
            magic < i,
            i <= n,
            result.len() == i,
            forall|j: int| 0 <= j < result.len() ==> #[trigger] result@[j]@.len() == n,
            forall|j: int| 0 <= j <= magic && j < result.len() ==> {
                let stars = magic - j;
                let diamonds = n - 2 * stars;
                #[trigger] result@[j]@ == repeat_char('*', stars as int) + repeat_char('D', diamonds as int) + repeat_char('*', stars as int)
            },
            forall|j: int| magic + 1 <= j && j < result.len() ==> {
                let u = j - magic;
                let stars = u;
                let diamonds = n - 2 * stars;
                #[trigger] result@[j]@ == repeat_char('*', stars as int) + repeat_char('D', diamonds as int) + repeat_char('*', stars as int)
            }
    {
        let u = i - magic;
        let stars = u;
        let diamonds = n - 2 * stars;
        let line = create_line(stars, diamonds);
        result.push(line);
        i += 1;
    }
    
    result
}
// </vc-code>


}

fn main() {}