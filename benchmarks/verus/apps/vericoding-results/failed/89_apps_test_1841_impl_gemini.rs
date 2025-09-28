// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(n: int, m: int, a: Seq<int>, queries: Seq<int>) -> bool {
    a.len() == n && queries.len() == m && n >= 1 && m >= 1 &&
    forall|i: int| 0 <= i < m ==> (#[trigger] queries[i], 1 <= queries[i] <= n).1
}

spec fn distinct_count(a: Seq<int>, start: int) -> int
    recommends 0 <= start < a.len()
{
    let suffix_indices = Set::new(|j: int| start <= j < a.len());
    let suffix_values = suffix_indices.map(|j: int| a[j]);
    suffix_values.len() as int
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): [added spec fn for i8] */
spec fn distinct_count_spec(a: Seq<i8>, start: int) -> int
    recommends 0 <= start < a.len()
{
    let suffix_indices = Set::new(|j: int| start <= j < a.len());
    let suffix_values = suffix_indices.map(|j: int| a[j]);
    suffix_values.len() as int
}

/* helper modified by LLM (iteration 2): [added lemma to relate i8 and int distinct counts] */
proof fn lemma_distinct_count_i8_is_int(a: Seq<i8>, start: int)
    requires 0 <= start < a.len()
    ensures distinct_count_spec(a, start) == distinct_count(a.map(|_i, v| v as int), start)
{
    let a_int = a.map(|_i, v| v as int);
    let indices = Set::new(|j: int| start <= j < a.len());
    let values_i8 = indices.map(|j: int| a[j]);
    let values_int = indices.map(|j: int| a_int[j]);
    
    let f = |v: i8| v as int;
    vstd::seq_lib::lemma_map_properties(a, |_i, v| v as int);
    
    assert(values_int == indices.map(|j| f(a[j])));
    vstd::set_lib::lemma_map_fusion(indices, |j| a[j], f);
    assert(values_i8.map(f) == indices.map(|j| f(a[j])));
    
    vstd::prover::assert_prover_witnesses_forall(|x: i8, y: i8| f(x) == f(y) ==> x == y);
    vstd::set_lib::lemma_len_map_injective(values_i8, f);
    assert(values_i8.len() == values_i8.map(f).len());
    assert(distinct_count_spec(a, start) == values_i8.len());
    assert(distinct_count(a_int, start) == values_int.len());
}

/* helper modified by LLM (iteration 2): [fixed compilation errors and proof logic] */
fn compute_distinct_count_for_suffix(a: &Vec<i8>, start_idx: i8) -> (count: i8)
    requires
        0 <= start_idx,
        (start_idx as usize) < a.len(),
        a.len() <= 127,
    ensures
        count as int == distinct_count_spec(a@, start_idx as int),
        0 <= count <= (a.len() - (start_idx as usize)) as i8,
{
    let n = a.len() as i8;

    let mut seen: vstd::collections::HashSet<i8> = vstd::collections::HashSet::new();
    let mut j = start_idx;
    while j < n
        invariant
            a.len() == n,
            start_idx <= j <= n,
            seen@ == a@.subseq(start_idx as int, j as int).to_set(),
        decreases n - j
    {
        let elem = a[j as usize];
        seen.insert(elem);
        proof {
            let sub = a@.subseq(start_idx as int, j as int);
            assert(sub.push(elem) == a@.subseq(start_idx as int, (j + 1) as int));
            vstd::seq_lib::lemma_push_to_set_is_insert(sub, elem);
        }
        j = j + 1;
    }
    
    let result_val = seen.len() as i8;

    proof {
        let suffix_seq = a@.subseq(start_idx as int, a.len() as int);
        assert(seen@ == suffix_seq.to_set());

        vstd::seq_lib::lemma_subseq_to_set(a@, start_idx as int, a.len() as int);
        let expected_set = Set::new(|k: int| start_idx as int <= k < a@.len()).map(|k: int| a@[k]);
        assert(suffix_seq.to_set() == expected_set);
        assert(distinct_count_spec(a@, start_idx as int) == expected_set.len());
        
        vstd::set_lib::lemma_len_of_to_set(suffix_seq);
        assert(seen.len() <= suffix_seq.len());
        assert(suffix_seq.len() == a.len() - start_idx as usize);
    }
    
    result_val
}
// </vc-helpers>

// <vc-spec>
fn solve(n: i8, m: i8, a: Vec<i8>, queries: Vec<i8>) -> (result: Vec<i8>)
    requires 
        valid_input(n as int, m as int, a@.map(|i, x| x as int), queries@.map(|i, x| x as int))
    ensures 
        result.len() == m &&
        (forall|i: int| 0 <= i < m ==> (#[trigger] result@[i], result@[i] as int == distinct_count(a@.map(|i, x| x as int), queries@[i] as int - 1)).1)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): [fixed compilation errors and proof logic] */
    let ghost a_int = a@.map(|_i, x| x as int);
    let ghost queries_int = queries@.map(|_i, x| x as int);

    let mut result: Vec<i8> = Vec::new();
    let mut i: i8 = 0;
    while i < m
        invariant
            0 <= i <= m,
            result.len() == i as usize,
            a@.map(|_i, x| x as int) == a_int,
            queries@.map(|_i, x| x as int) == queries_int,
            valid_input(n as int, m as int, a_int, queries_int),
            forall|j: int| 0 <= j < i as int ==> #[trigger] result@[j] as int ==
                distinct_count(a_int, queries_int[j] - 1),
        decreases m - i
    {
        let q_val = queries[i as usize];
        let start_idx = q_val - 1;

        let count = compute_distinct_count_for_suffix(&a, start_idx);
        result.push(count);

        proof {
            lemma_distinct_count_i8_is_int(a@, start_idx as int);
        
            assert_forall_by(|j: int| {
                requires(0 <= j < (i + 1) as int);
                ensures(result@.push(count)@[j] as int == distinct_count(a_int, queries_int[j] - 1));
                
                if j < i as int {
                    assert(result@.push(count)@[j] == result@[j]);
                } else { // j == i
                    assert(result@.push(count)@[i] == count);
                    assert(queries_int[i] - 1 == start_idx as int);
                    assert(count as int == distinct_count_spec(a@, start_idx as int));
                    assert(distinct_count_spec(a@, start_idx as int) == distinct_count(a_int, start_idx as int));
                    assert(count as int == distinct_count(a_int, queries_int[i] - 1));
                }
            });
        }
        
        i = i + 1;
    }
    result
}
// </vc-code>


}

fn main() {}