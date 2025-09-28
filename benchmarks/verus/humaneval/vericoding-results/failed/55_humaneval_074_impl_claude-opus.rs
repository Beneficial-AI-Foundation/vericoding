// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn total_chars(lst: Seq<Seq<char>>) -> nat
    decreases lst.len()
{
    if lst.len() == 0 {
        0
    } else {
        lst[0].len() + total_chars(lst.subrange(1, lst.len() as int))
    }
}
// </vc-preamble>

// <vc-helpers>
proof fn lemma_total_chars_sum(lst: Seq<Seq<char>>, i: nat)
    requires
        i <= lst.len(),
    ensures
        total_chars(lst.subrange(0, i as int)) + total_chars(lst.subrange(i as int, lst.len() as int)) == total_chars(lst),
    decreases lst.len() - i
{
    /* helper modified by LLM (iteration 5): Fixed proof structure for lemma */
    if i == lst.len() {
        assert(lst.subrange(i as int, lst.len() as int).len() == 0);
        assert(total_chars(lst.subrange(i as int, lst.len() as int)) == 0);
        assert(lst.subrange(0, i as int) =~= lst);
        assert(total_chars(lst.subrange(0, i as int)) == total_chars(lst));
    } else if i == 0 {
        assert(lst.subrange(0, 0).len() == 0);
        assert(total_chars(lst.subrange(0, 0)) == 0);
        assert(lst.subrange(0, lst.len() as int) =~= lst);
    } else {
        lemma_total_chars_sum(lst, i - 1);
        assert(lst.subrange(0, i as int) =~= lst.subrange(0, (i - 1) as int).push(lst[(i - 1) as int]));
        assert(total_chars(lst.subrange(0, i as int)) == total_chars(lst.subrange(0, (i - 1) as int)) + lst[(i - 1) as int].len());
    }
}
// </vc-helpers>

// <vc-spec>
fn total_match(lst1: Vec<Vec<char>>, lst2: Vec<Vec<char>>) -> (result: Vec<Vec<char>>)
    ensures 
        result@ == lst1@ || result@ == lst2@,
        total_chars(lst1@.map_values(|v: Vec<char>| v@)) <= total_chars(lst2@.map_values(|v: Vec<char>| v@)) ==> result@ == lst1@,
        total_chars(lst1@.map_values(|v: Vec<char>| v@)) > total_chars(lst2@.map_values(|v: Vec<char>| v@)) ==> result@ == lst2@
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed nat type usage - using usize instead */
    let mut sum1: usize = 0;
    let mut sum2: usize = 0;
    let mut i: usize = 0;
    
    while i < lst1.len()
        invariant
            i <= lst1.len(),
            sum1 == total_chars(lst1@.subrange(0, i as int).map_values(|v: Vec<char>| v@)) as usize,
            sum1 <= usize::MAX,
        decreases lst1.len() - i
    {
        let old_sum1 = sum1;
        let item_len = lst1[i].len();
        sum1 = sum1 + item_len;
        
        proof {
            assert(lst1@.subrange(0, (i + 1) as int).map_values(|v: Vec<char>| v@) =~=
                   lst1@.subrange(0, i as int).map_values(|v: Vec<char>| v@).push(lst1[i as int]@));
            assert(total_chars(lst1@.subrange(0, (i + 1) as int).map_values(|v: Vec<char>| v@)) ==
                   total_chars(lst1@.subrange(0, i as int).map_values(|v: Vec<char>| v@)) + lst1[i as int]@.len());
        }
        i = i + 1;
    }
    assert(lst1@.subrange(0, lst1.len() as int) =~= lst1@);
    
    i = 0;
    while i < lst2.len()
        invariant
            i <= lst2.len(),
            sum2 == total_chars(lst2@.subrange(0, i as int).map_values(|v: Vec<char>| v@)) as usize,
            sum2 <= usize::MAX,
        decreases lst2.len() - i
    {
        let old_sum2 = sum2;
        let item_len = lst2[i].len();
        sum2 = sum2 + item_len;
        
        proof {
            assert(lst2@.subrange(0, (i + 1) as int).map_values(|v: Vec<char>| v@) =~=
                   lst2@.subrange(0, i as int).map_values(|v: Vec<char>| v@).push(lst2[i as int]@));
            assert(total_chars(lst2@.subrange(0, (i + 1) as int).map_values(|v: Vec<char>| v@)) ==
                   total_chars(lst2@.subrange(0, i as int).map_values(|v: Vec<char>| v@)) + lst2[i as int]@.len());
        }
        i = i + 1;
    }
    assert(lst2@.subrange(0, lst2.len() as int) =~= lst2@);
    
    if sum1 <= sum2 {
        lst1
    } else {
        lst2
    }
}
// </vc-code>


}

fn main() {}