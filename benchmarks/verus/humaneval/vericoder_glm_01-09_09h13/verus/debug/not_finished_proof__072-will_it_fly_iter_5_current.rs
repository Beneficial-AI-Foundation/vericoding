use vstd::prelude::*;

verus! {

// pure-end

spec fn spec_sum(s: Seq<u32>) -> (ret:int) {
    s.fold_left(0, |x: int, y| x + y)
}
// pure-end

// <vc-helpers>
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
// </vc-helpers>

// <vc-spec>
fn will_it_fly(qs: &Vec<u32>, w: u32) -> (ret: bool)
    // post-conditions-start
    ensures
        ret <==> qs@ =~= qs@.reverse() && spec_sum(qs@) <= w,
    // post-conditions-end
// </vc-spec>
// <vc-code>
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
// </vc-code>

fn main() {}
}