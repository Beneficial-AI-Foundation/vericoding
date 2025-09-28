// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn sum(s: Seq<int>) -> int
    decreases s.len()
{
    if s.len() == 0 { 0 } else { s[0] + sum(s.subrange(1, s.len() as int)) }
}

spec fn ceil(f: int) -> int {
    f + 1
}

spec fn square_seq(lst: Seq<int>) -> Seq<int> {
    Seq::new(lst.len(), |i: int| ceil(lst[i]) * ceil(lst[i]))
}
// </vc-preamble>

// <vc-helpers>
proof fn lemma_vector_index_eq(v: Vec<i8>, i: usize) 
    requires 
        0 <= i < v.len(),
    ensures 
        v@[i as int] == v[i] as int,
{
    vstd::pervasive::assert_by(v@.index(i as int) == v[i] as int, {
        assert(v@[i as int] == v[i] as int) by (vstd::view::lemma_vec_index_view(v, i));
    });
}

proof fn lemma_vec_index_view_helper(v: Vec<i8>, i: usize)
    requires
        0 <= i < v.len(),
    ensures
        v@[i as int] == v[i] as int,
{
    vstd::view::lemma_vec_index_view(v, i);
}
// </vc-helpers>

// <vc-spec>
fn sum_squares(lst: Vec<i8>) -> (r: i8)
    ensures r as int == sum(square_seq(lst@.map(|i: int, x: i8| x as int)))
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed integer casting using ghost lemma and proper sequence handling */
    let mut result: i8 = 0;
    let mut i: usize = 0;
    
    while i < lst.len()
        invariant
            0 <= i && i <= lst.len(),
            result as int == sum(square_seq(vec_to_seq(lst).subrange(0, i as int))),
    {
        let x = lst[i];
        proof {
            lemma_vector_index_eq(lst, i);
        }
        let squared_val: int = (x as int + 1) * (x as int + 1);
        let squared: i8 = squared_val as i8;
        
        result = ((result as i16) + (squared as i16)) as i8;
        i += 1;
    }
    
    result
}
// </vc-code>


}

fn main() {}