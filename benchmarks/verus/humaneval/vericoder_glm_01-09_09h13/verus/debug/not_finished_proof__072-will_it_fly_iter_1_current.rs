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
        assert(s.drop_last() =~= s.drop_last().reverse());
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
    let mut i = 0;
    let mut j = qs.len() as int;
    let mut sum = 0;
    
    while i < j
        invariant
            0 <= i <= j <= qs@.len(),
            spec_sum(qs@.subrange(i as int, j as int)) + sum <= w,
            qs@.subrange(0, i) =~= qs@.subrange(j, qs@.len()).reverse(),
    {
        if i == j - 1 {
            assert(qs@.subrange(i, j) == seq![qs@[i]]);
            sum = sum + (qs@[i] as int);
            i = i + 1;
            j = j - 1;
            assert(sum <= w);
            
            assert(qs@.subrange(0, i) =~= qs@.subrange(j, qs@.len()).reverse());
        } else {
            assert(qs@[i] == qs@[j - 1]);
            sum = sum + (qs@[i] as int) + (qs@[j - 1] as int);
            i = i + 1;
            j = j - 1;
            
            assert(qs@.subrange(0, i) =~= qs@.subrange(j, qs@.len()).reverse());
        }
    }
    
    if i != j {
        lemma_seq_reverse_self(qs@.subrange(0, i));
        assert(qs@ =~= qs@.subrange(0, i) + qs@.subrange(i, j) + qs@.subrange(j, qs@.len()));
        assert(qs@ =~= qs@.subrange(0, i) + qs@.subrange(j, qs@.len()));
        assert(qs@ =~= qs@.subrange(j, qs@.len()) + qs@.subrange(0, i));
        assert(qs@ =~= qs@.subrange(j, qs@.len()).reverse() + qs@.subrange(0, i));
        assert(qs@ =~= qs@.subrange(0, i).reverse() + qs@.subrange(0, i));
        assert(qs@ =~= qs@.subrange(0, i).reverse() + qs@.subrange(0, i).reverse());
        assert(qs@ =~= (qs@.subrange(0, i) + qs@.subrange(0, i).reverse()).reverse());
        assert(qs@ =~= qs@.reverse());
        
        assert(spec_sum(qs@) == spec_sum(qs@.subrange(0, i)) + spec_sum(qs@.subrange(i, j)) + spec_sum(qs@.subrange(j, qs@.len())));
        assert(spec_sum(qs@) == spec_sum(qs@.subrange(0, i)) + 0 + spec_sum(qs@.subrange(j, qs@.len())));
        assert(spec_sum(qs@) == spec_sum(qs@.subrange(0, i)) + spec_sum(qs@.subrange(j, qs@.len())));
        assert(spec_sum(qs@) == spec_sum(qs@.subrange(0, i)) + spec_sum(qs@.subrange(0, i).reverse()));
        assert(qs@.subrange(0, i) =~= qs@.subrange(0, i).reverse());
        assert(spec_sum(qs@.subrange(0, i)) == spec_sum(qs@.subrange(0, i).reverse()));
        assert(spec_sum(qs@) == spec_sum(qs@.subrange(0, i)) + spec_sum(qs@.subrange(0, i)));
        assert(sum == 2 * spec_sum(qs@.subrange(0, i)));
        assert(spec_sum(qs@) <= w);
    } else {
        lemma_seq_reverse_self(qs@.subrange(0, i));
        assert(qs@ =~= qs@.subrange(0, i) + qs@.subrange(i, j) + qs@.subrange(j, qs@.len()));
        assert(qs@ =~= qs@.subrange(0, i) + seq![qs@[i]] + qs@.subrange(j, qs@.len()));
        assert(qs@ =~= qs@.subrange(0, i) + qs@.subrange(j, qs@.len()));
        assert(qs@ =~= qs@.subrange(j, qs@.len()) + qs@.subrange(0, i));
        assert(qs@ =~= qs@.subrange(j, qs@.len()).reverse() + qs@.subrange(0, i));
        assert(qs@ =~= qs@.subrange(0, i).reverse() + qs@.subrange(0, i));
        assert(qs@ =~= qs@.subrange(0, i).reverse() + seq![qs@[i]] + qs@.subrange(0, i));
        assert(qs@ =~= (qs@.subrange(0, i).push(qs@[i]) + qs@.subrange(0, i)).reverse());
        assert(qs@ =~= (qs@.subrange(0, i + 1) + qs@.subrange(0, i)).reverse());
        lemma_seq_reverse_self(qs@.subrange(0, i));
        lemma_seq_reverse_self(qs@.subrange(0, i + 1));
        assert(qs@ =~= qs@.subrange(0, i).reverse() + seq![qs@[i]] + qs@.subrange(0, i));
        assert(qs@ =~= qs@.subrange(0, i).reverse() + qs@.subrange(0, i + 1));
        lemma_seq_reverse_self(qs@.subrange(0, i));
        assert(qs@ =~= qs@.subrange(0, i + 1).reverse());
        lemma_seq_reverse_self(qs@.subrange(0, i + 1));
        
        assert(spec_sum(qs@) == spec_sum(qs@.subrange(0, i)) + spec_sum(qs@.subrange(i, j)) + spec_sum(qs@.subrange(j, qs@.len())));
        assert(spec_sum(qs@) == spec_sum(qs@.subrange(0, i)) + (qs@[i] as int) + spec_sum(qs@.subrange(j, qs@.len())));
        assert(spec_sum(qs@) == spec_sum(qs@.subrange(0, i)) + (qs@[i] as int) + spec_sum(qs@.subrange(0, i)));
        assert(spec_sum(qs@) == (qs@[i] as int) + 2 * spec_sum(qs@.subrange(0, i)));
        assert(sum == (qs@[i] as int) + 2 * spec_sum(qs@.subrange(0, i)));
        assert(spec_sum(qs@) <= w);
    }
}
// </vc-code>

fn main() {}
}