use vstd::prelude::*;

verus! {

// pure-end

spec fn spec_sum(s: Seq<u32>) -> (ret:int) {
    s.fold_left(0, |x: int, y| x + y)
}
// pure-end

// <vc-helpers>
proof fn lemma_seq_reverse_self<T>(s: Seq<T>)
    ensures
        s =~= s.reverse()
{
    if s.len() == 0 {
        assert(s =~= s.reverse());
    } else {
        lemma_seq_reverse_self(s.drop_last());
        assert(s =~= s.drop_last().push(s.last()));
        assert(s.reverse() =~= s.reverse().drop_last().push(s.reverse().last()));
        assert(s.reverse().drop_last() =~= s.drop_last().reverse());
        assert(s.reverse().last() == s.first());
        assert(s.last() == s.reverse().first());
    }
}

proof fn lemma_spec_sum_add_last(s: Seq<u32>) 
    requires
        s.len() > 0,
    ensures
        spec_sum(s) == spec_sum(s.drop_last()) + (s.last() as int),
{
    assert(s =~= s.drop_last() + seq![s.last()]);
    assert(spec_sum(s) == spec_sum(s.drop_last()) + spec_sum(seq![s.last()]));
    assert(spec_sum(seq![s.last()]) == (s.last() as int));
}

proof fn lemma_spec_sum_subrange_split(s: Seq<u32>, i: int, j: int, k: int)
    requires
        0 <= i <= j <= k <= s.len(),
    ensures
        spec_sum(s.subrange(i, k)) == spec_sum(s.subrange(i, j)) + spec_sum(s.subrange(j, k)),
{
    assert(s.subrange(i, k) =~= s.subrange(i, j) + s.subrange(j, k));
    assert(spec_sum(s.subrange(i, k)) == spec_sum(s.subrange(i, j) + s.subrange(j, k)));
    assert(spec_sum(s.subrange(i, j) + s.subrange(j, k)) == spec_sum(s.subrange(i, j)) + spec_sum(s.subrange(j, k)));
}

proof fn lemma_spec_sum_reverse(s: Seq<u32>)
    ensures
        spec_sum(s) == spec_sum(s.reverse()),
{
    if s.len() == 0 {
    } else if s.len() == 1 {
        assert(s =~= s.reverse());
    } else {
        lemma_spec_sum_reverse(s.drop_last());
        lemma_spec_sum_add_last(s);
        lemma_spec_sum_add_last(s.reverse());
        assert(s.reverse().drop_last() =~= s.drop_last().reverse());
        assert(spec_sum(s.reverse().drop_last()) == spec_sum(s.drop_last().reverse()));
        assert(spec_sum(s.drop_last().reverse()) == spec_sum(s.drop_last()));
        assert(spec_sum(s.reverse()) == spec_sum(s.reverse().drop_last()) + (s.reverse().last() as int));
        assert(s.reverse().last() == s.first());
        assert(spec_sum(s.reverse()) == spec_sum(s.drop_last()) + (s.first() as int));
        assert(spec_sum(s) == spec_sum(s.drop_last()) + (s.last() as int));
    }
}
// </vc-helpers>

// <vc-spec>
fn will_it_fly(qs: &Vec<u32>, w: u32) -> (ret: bool)
    // post-conditions-start
    ensures
        ret <==> qs@ =~= qs@.reverse() && spec_sum(qs@) <= w,
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    let mut i = 0usize;
    let mut j = qs.len();
    let mut sum = 0u32;
    
    while i < j
        invariant
            0 <= i <= j <= qs@.len(),
            spec_sum(qs@.subrange(i as int, j as int)) + (sum as int) <= (w as int),
            qs@.subrange(0, i) =~= qs@.subrange(j, qs@.len()).reverse(),
    {
        if i == j - 1 {
            sum = sum + qs@[i];
            proof {
                lemma_spec_sum_subrange_split(qs@, 0, i as int, (i + 1) as int);
                lemma_spec_sum_subrange_split(qs@, (i + 1) as int, j as int, qs@.len() as int);
            }
            i = i + 1;
            j = j - 1;
        } else {
            assert(qs@[i] == qs@[j - 1]);
            sum = sum + qs@[i] + qs@[j - 1];
            proof {
                lemma_spec_sum_subrange_split(qs@, 0, i as int, (i + 1) as int);
                lemma_spec_sum_subrange_split(qs@, (i + 1) as int, (j - 1) as int, j as int);
                lemma_spec_sum_subrange_split(qs@, j as int, qs@.len() as int, qs@.len() as int);
            }
            i = i + 1;
            j = j - 1;
        }
    }
    
    if i != j {
        false
    } else {
        lemma_seq_reverse_self(qs@.subrange(0, i));
        lemma_seq_reverse_self(qs@.subrange(i, qs@.len() as int));
        
        assert(qs@ =~= qs@.subrange(0, i) + qs@.subrange(i, j) + qs@.subrange(j, qs@.len() as int));
        assert(qs@ =~= qs@.subrange(0, i) + qs@.subrange(j, qs@.len() as int));
        assert(qs@ =~= qs@.subrange(j, qs@.len() as int) + qs@.subrange(0, i));
        assert(qs@ =~= qs@.subrange(j, qs@.len() as int).reverse() + qs@.subrange(0, i));
        assert(qs@ =~= qs@.subrange(0, i).reverse() + qs@.subrange(0, i));
        
        proof {
            lemma_spec_sum_subrange_split(qs@, 0, i as int, j as int);
            lemma_spec_sum_subrange_split(qs@, i as int, j as int, qs@.len() as int);
        }
        assert(spec_sum(qs@) == spec_sum(qs@.subrange(0, i)) + spec_sum(qs@.subrange(j, qs@.len() as int)));
        
        lemma_spec_sum_reverse(qs@.subrange(0, i));
        assert(spec_sum(qs@.subrange(0, i)) == spec_sum(qs@.subrange(0, i).reverse()));
        assert(spec_sum(qs@) == spec_sum(qs@.subrange(0, i)) + spec_sum(qs@.subrange(0, i).reverse()));
        assert(spec_sum(qs@) == 2 * spec_sum(qs@.subrange(0, i)));
        assert((sum as int) == 2 * spec_sum(qs@.subrange(0, i)));
        assert(spec_sum(qs@) <= (w as int));
        true
    }
}
// </vc-code>

fn main() {}
}