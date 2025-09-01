use vstd::prelude::*;

verus! {

spec fn zip_halves<T>(v: Seq<T>) -> (ret: Seq<(T, T)>) {
    v.take((v.len() / 2) as int).zip_with(v.skip(((v.len() + 1) / 2) as int).reverse())
}
// pure-end
// pure-end

spec fn diff(s: Seq<(i32, i32)>) -> (ret: int) {
    s.fold_left(
        0,
        |acc: int, x: (i32, i32)|
            if (x.0 != x.1) {
                acc + 1
            } else {
                acc
            },
    )
}
// pure-end

// <vc-helpers>
proof fn lemma_zip_halves_len<T>(v: Seq<T>)
    ensures
        zip_halves(v).len() == (v.len() / 2) as int,
{
    let first_half = v.take((v.len() / 2) as int);
    let second_half = v.skip(((v.len() + 1) / 2) as int).reverse();
    
    assert(first_half.len() == (v.len() / 2) as int);
    assert(second_half.len() == v.len() - ((v.len() + 1) / 2) as int);
    
    if v.len() % 2 == 0 {
        assert(((v.len() + 1) / 2) as int == (v.len() / 2) as int);
        assert(second_half.len() == (v.len() / 2) as int);
    } else {
        assert(((v.len() + 1) / 2) as int == (v.len() / 2) as int + 1);
        assert(second_half.len() == (v.len() / 2) as int);
    }
}

proof fn lemma_zip_halves_index<T>(v: Seq<T>, i: int)
    requires
        0 <= i < zip_halves(v).len(),
    ensures
        zip_halves(v)[i] == (v[i], v[v.len() - 1 - i]),
{
    let first_half = v.take((v.len() / 2) as int);
    let second_half = v.skip(((v.len() + 1) / 2) as int).reverse();
    let zipped = first_half.zip_with(second_half);
    
    assert(zipped[i] == (first_half[i], second_half[i]));
    assert(first_half[i] == v[i]);
    
    let skip_len = ((v.len() + 1) / 2) as int;
    let skipped = v.skip(skip_len);
    assert(second_half[i] == skipped[skipped.len() - 1 - i]);
    assert(skipped[skipped.len() - 1 - i] == v[skip_len + skipped.len() - 1 - i]);
    assert(skipped.len() == v.len() - skip_len);
    assert(skip_len + skipped.len() - 1 - i == v.len() - 1 - i);
}

proof fn lemma_diff_step(s: Seq<(i32, i32)>, x: (i32, i32))
    ensures
        diff(s.push(x)) == diff(s) + if x.0 != x.1 { 1 } else { 0 },
{
    let f = |acc: int, y: (i32, i32)| if y.0 != y.1 { acc + 1 } else { acc };
    
    assert(s.push(x).fold_left(0, f) == s.fold_left(0, f) + if x.0 != x.1 { 1 } else { 0 }) by {
        s.lemma_fold_left_alt(0, f);
        s.push(x).lemma_fold_left_alt(0, f);
    };
}
// </vc-helpers>

// <vc-spec>
fn smallest_change(v: Vec<i32>) -> (change: usize)
    // pre-conditions-start
    requires
        v@.len() < usize::MAX,
    // pre-conditions-end
    // post-conditions-start
    ensures
        change == diff(zip_halves(v@)),
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    let len = v.len();
    let half_len = len / 2;
    
    proof {
        lemma_zip_halves_len(v@);
    }
    
    let mut change: usize = 0;
    let mut i: usize = 0;
    
    while i < half_len
        invariant
            0 <= i <= half_len,
            half_len == len / 2,
            change as int == diff(zip_halves(v@).take(i as int)),
            len == v@.len(),
            change <= i,
        decreases half_len - i,
    {
        let left_val = v[i];
        let right_val = v[len - 1 - i];
        
        proof {
            lemma_zip_halves_index(v@, i as int);
            let current_pair = (left_val, right_val);
            let prev_seq = zip_halves(v@).take(i as int);
            let curr_seq = zip_halves(v@).take((i + 1) as int);
            
            assert(curr_seq == prev_seq.push(zip_halves(v@)[i as int]));
            assert(zip_halves(v@)[i as int] == current_pair);
            
            lemma_diff_step(prev_seq, current_pair);
        }
        
        if left_val != right_val {
            change = change + 1;
        }
        
        i = i + 1;
    }
    
    proof {
        assert(i == half_len);
        assert(zip_halves(v@).take(half_len as int) == zip_halves(v@));
    }
    
    change
}
// </vc-code>

fn main() {}
}