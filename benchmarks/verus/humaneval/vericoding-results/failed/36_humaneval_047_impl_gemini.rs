// <vc-preamble>
use vstd::prelude::*;
use vstd::multiset::*;

verus! {

spec fn insert_sorted(x: int, sorted: Seq<int>) -> Seq<int>
    decreases sorted.len()
{
    if sorted.len() == 0 {
        seq![x]
    } else if x <= sorted[0] {
        seq![x].add(sorted)
    } else {
        seq![sorted[0]].add(insert_sorted(x, sorted.subrange(1, sorted.len() as int)))
    }
}

spec fn sort(s: Seq<int>) -> Seq<int>
    decreases s.len()
{
    if s.len() == 0 {
        seq![]
    } else {
        insert_sorted(s[0], sort(s.subrange(1, s.len() as int)))
    }
}

spec fn is_sorted(s: Seq<int>) -> bool {
    forall|i: int, j: int| 0 <= i < j < s.len() ==> s[i] <= s[j]
}

spec fn multiset_from_seq(s: Seq<int>) -> Multiset<int>
    decreases s.len()
{
    if s.len() == 0 {
        Multiset::empty()
    } else {
        Multiset::singleton(s[0]).add(multiset_from_seq(s.subrange(1, s.len() as int)))
    }
}

spec fn valid_input(l: Seq<int>) -> bool {
    l.len() > 0
}

spec fn median_value(l: Seq<int>) -> int {
    if l.len() == 0 {
        0int
    } else {
        let sorted_list = sort(l);
        let n = sorted_list.len();
        if n % 2 == 1 {
            sorted_list[(n / 2) as int]
        } else {
            (sorted_list[(n / 2 - 1) as int] + sorted_list[(n / 2) as int]) / 2
        }
    }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): [removed redundant 'as int' casts] */
proof fn lemma_is_sorted_insert_sorted(x: int, s: Seq<int>)
    requires is_sorted(s)
    ensures is_sorted(insert_sorted(x, s))
    decreases s.len()
{
    if s.len() > 0 && x > s[0] {
        lemma_is_sorted_insert_sorted(x, s.subrange(1, s.len()));
    }
}

/* helper modified by LLM (iteration 5): [removed redundant 'as int' casts] */
proof fn lemma_multiset_insert_sorted(x: int, s: Seq<int>)
    ensures multiset_from_seq(insert_sorted(x, s)) == Multiset::singleton(x).add(multiset_from_seq(s))
    decreases s.len()
{
    if s.len() > 0 && x > s[0] {
         lemma_multiset_insert_sorted(x, s.subrange(1, s.len()));
    }
}

/* helper modified by LLM (iteration 5): [removed redundant 'as int' casts] */
proof fn lemma_is_sorted_sort(s: Seq<int>)
    ensures is_sorted(sort(s))
    decreases s.len()
{
    if s.len() > 0 {
        let sub_sort = sort(s.subrange(1, s.len()));
        lemma_is_sorted_sort(s.subrange(1, s.len()));
        lemma_is_sorted_insert_sorted(s[0], sub_sort);
    }
}

/* helper modified by LLM (iteration 5): [removed redundant 'as int' casts] */
proof fn lemma_multiset_sort(s: Seq<int>)
    ensures multiset_from_seq(sort(s)) == multiset_from_seq(s)
    decreases s.len()
{
    if s.len() > 0 {
        let sub = s.subrange(1, s.len());
        let sorted_sub = sort(sub);
        lemma_multiset_sort(sub);
        lemma_multiset_insert_sorted(s[0], sorted_sub);
    }
}

/* helper modified by LLM (iteration 5): [removed redundant 'as int' casts] */
fn exec_insert_sorted(x: int, v_sorted: &Vec<int>) -> (res: Vec<int>)
    requires is_sorted(v_sorted.view())
    ensures
        res.view() == insert_sorted(x, v_sorted.view()),
        is_sorted(res.view()),
        multiset_from_seq(res.view()) == multiset_from_seq(v_sorted.view()).add(Multiset::singleton(x)),
    decreases v_sorted.len()
{
    lemma_is_sorted_insert_sorted(x, v_sorted.view());
    lemma_multiset_insert_sorted(x, v_sorted.view());
    let v_view = v_sorted.view();

    if v_view.len() == 0 {
        let mut res = Vec::new();
        res.push(x);
        return res;
    }

    if x <= v_view[0] {
        let mut res = Vec::with_capacity((v_sorted.len() + 1) as usize);
        res.push(x);
        res.extend_from_slice(v_sorted.as_slice());
        return res;
    } else {
        let sub_vec = v_sorted.subvec(1, v_sorted.len());
        let inserted_sub = exec_insert_sorted(x, &sub_vec);

        let mut res = Vec::new();
        res.push(v_view[0]);
        res.extend_from_slice(inserted_sub.as_slice());
        
        assert(sub_vec.view() == v_view.subrange(1, v_view.len()));
        assert(inserted_sub.view() == insert_sorted(x, sub_vec.view()));
        assert(res.view() == seq![v_view[0]].add(inserted_sub.view()));
        
        return res;
    }
}

/* helper modified by LLM (iteration 5): [Fixed compilation error by removing 'as int' cast] */
fn exec_sort(s: Seq<int>) -> (res: Vec<int>)
    ensures
        is_sorted(res.view()),
        multiset_from_seq(res.view()) == multiset_from_seq(s),
        res.view() == sort(s),
    decreases s.len()
{
    lemma_is_sorted_sort(s);
    lemma_multiset_sort(s);

    if s.len() == 0 {
        return Vec::new();
    }

    let sorted_sub = exec_sort(s.subrange(1, s.len()));
    let res = exec_insert_sorted(s[0], &sorted_sub);
    assert(res.view() == sort(s));
    return res;
}
// </vc-helpers>

// <vc-spec>
fn median(l: Seq<int>) -> (result: int)
    requires valid_input(l)
    ensures 
        result == median_value(l) &&
        ({
            let sorted_list = sort(l);
            let n = sorted_list.len();
            n % 2 == 1 ==> result == sorted_list[(n / 2) as int]
        }) &&
        ({
            let sorted_list = sort(l);
            let n = sorted_list.len();
            n % 2 == 0 ==> result == (sorted_list[(n / 2 - 1) as int] + sorted_list[(n / 2) as int]) / 2
        }) &&
        is_sorted(sort(l)) &&
        multiset_from_seq(sort(l)) == multiset_from_seq(l) &&
        (l.len() == 1 ==> result == l[0])
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): [Fix exec/ghost variable confusion] */
    let sorted_vec = exec_sort(l);

    lemma_is_sorted_sort(l);
    lemma_multiset_sort(l);
    
    let n_usize = sorted_vec.len();
    let ghost n_int = l.len() as int;
    assert(sorted_vec.view() == sort(l));
    assert(sorted_vec.view().len() == l.len());
    assert(n_usize as int == n_int);

    let ghost sorted_list_spec = sort(l);
    
    if n_usize % 2 == 1 {
        let mid_index = n_usize / 2;
        let median_val = sorted_vec[mid_index];
        
        assert(mid_index as int == n_int / 2);
        assert(median_val == sorted_list_spec[n_int / 2]);
        
        return median_val;
    } else {
        assert(n_int >= 2); 
        let idx1 = n_usize / 2 - 1;
        let idx2 = n_usize / 2;
        let median_val = (sorted_vec[idx1] + sorted_vec[idx2]) / 2;

        assert(idx1 as int == n_int / 2 - 1);
        assert(idx2 as int == n_int / 2);
        assert(sorted_vec[idx1] == sorted_list_spec[n_int / 2 - 1]);
        assert(sorted_vec[idx2] == sorted_list_spec[n_int / 2]);
        
        return median_val;
    }
}
// </vc-code>


}

fn main() {}