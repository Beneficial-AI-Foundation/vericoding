// <vc-preamble>
use vstd::prelude::*;

verus! {

type BiggestMap = Map<int, int>;
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fix sequence indexing syntax */
fn count_occurrences(a: Seq<i8>, value: i8) -> (count: usize)
    ensures count == Set::new(|j: int| 0 <= j < a.len() && a[j] as int == value as int).len()
{
    let mut count: usize = 0;
    let mut i: usize = 0;
    while i < a.len() as usize
        invariant
            0 <= i <= a.len(),
            count == Set::new(|j: int| 0 <= j < i && a[j] as int == value as int).len(),
        decreases a.len() - i
    {
        if a[i as int] == value {
            count = count + 1;
        }
        i = i + 1;
    }
    count
}
// </vc-helpers>

// <vc-spec>
fn count(a: Vec<i8>) -> (biggest: BiggestMap)
  ensures forall|i: int| 0 <= i < a@.len() && biggest.dom().contains(a@[i] as int) ==>
    #[trigger] biggest[a@[i] as int] == Set::new(|j: int| 0 <= j < a@.len() && a@[j] as int == a@[i] as int).len()
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): cast count to int for map insertion */
    let mut result: BiggestMap = Map::empty();
    let mut i: usize = 0;
    
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            forall|value: int| result.dom().contains(value) ==> 
                result[value] == Set::new(|j: int| 0 <= j < i && a@[j] as int == value).len(),
        decreases a.len() - i
    {
        let value = a[i];
        let count = count_occurrences(a@, value);
        let value_int = value as int;
        result = result.insert(value_int, count as int);
        i = i + 1;
    }
    
    result
}
// </vc-code>


}

fn main() {}