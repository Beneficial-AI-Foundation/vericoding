use vstd::prelude::*;

verus! {

spec fn zip_halves<T>(v: Seq<T>) -> (ret: Seq<(T, T)>) {
    v.take((v.len() / 2) as int).zip_with(v.skip(((v.len() + 1) / 2) as int).reverse())
}
// pure-end

/* code modified by LLM (iteration 1): fixed closure syntax for Rust/Verus compatibility */
spec fn diff(s: Seq<(i32, i32)>) -> (ret: int) {
    s.fold_left(
        0,
        |acc: int, x: (i32, i32)|
            if x.0 != x.1 {
                acc + 1
            } else {
                acc
            },
    )
}
// pure-end

/* code modified by LLM (iteration 1): added helper lemma to establish relationship between loop iteration and spec */
proof fn lemma_zip_halves_index<T>(v: Seq<T>, i: int)
    requires
        0 <= i < v.len() / 2,
    ensures
        zip_halves(v)[i] == (v[i], v[v.len() - 1 - i]),
{
    let first_half = v.take((v.len() / 2) as int);
    let second_half = v.skip(((v.len() + 1) / 2) as int).reverse();
    
    assert(first_half[i] == v[i]);
    assert(second_half[i] == v[v.len() - 1 - i]);
}

/* code modified by LLM (iteration 1): added helper lemma for diff property with corrected syntax */
proof fn lemma_diff_extend(s: Seq<(i32, i32)>, elem: (i32, i32))
    ensures
        diff(s.push(elem)) == diff(s) + (if elem.0 != elem.1 { 1 } else { 0 }),
{
    assert(s.push(elem).fold_left(0, |acc: int, x: (i32, i32)| if x.0 != x.1 { acc + 1 } else { acc }) 
           == s.fold_left(0, |acc: int, x: (i32, i32)| if x.0 != x.1 { acc + 1 } else { acc }) + (if elem.0 != elem.1 { 1 } else { 0 }));
}

//IMPL smallest_change
fn smallest_change(v: Vec<i32>) -> (change: usize)
    // pre-conditions-start
    requires
        v@.len() < usize::MAX,
    // pre-conditions-end
    // post-conditions-start
    ensures
        change == diff(zip_halves(v@)),
    // post-conditions-end
{
    let len = v.len();
    let first_half_len = len / 2;
    let second_half_start = (len + 1) / 2;
    
    let mut count = 0;
    let mut i = 0;
    
    /* code modified by LLM (iteration 1): enhanced loop with proper invariants and overflow protection */
    while i < first_half_len
        invariant
            i <= first_half_len,
            first_half_len == len / 2,
            second_half_start == (len + 1) / 2,
            len == v@.len(),
            count == diff(zip_halves(v@).take(i as int)),
            count <= i,
        decreases first_half_len - i
    {
        let left_idx = i;
        let right_idx = len - 1 - i;
        
        /* code modified by LLM (iteration 1): establish relationship between current indices and zip_halves */
        proof {
            lemma_zip_halves_index(v@, i as int);
            let current_pair = (v@[i as int], v@[(len - 1 - i) as int]);
            let extended_seq = zip_halves(v@).take(i as int).push(current_pair);
            assert(extended_seq == zip_halves(v@).take((i + 1) as int));
            lemma_diff_extend(zip_halves(v@).take(i as int), current_pair);
        }
        
        if v[left_idx] != v[right_idx] {
            /* code modified by LLM (iteration 1): added overflow check */
            assert(count < usize::MAX); // This follows from count <= i < first_half_len < len < usize::MAX
            count += 1;
        }
        i += 1;
    }
    
    count
}

}
fn main() {}