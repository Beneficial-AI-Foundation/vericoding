use vstd::prelude::*;

spec fn is_sorted(s: Seq<int>) -> bool {
    forall|i: int| 0 <= i < s.len()-1 ==> s[i] <= s[i+1]
}

spec fn sort_spec(input: Seq<int>, output: Seq<int>) -> bool {
    && is_sorted(output)
    && output.to_multiset() == input.to_multiset()
}

pub fn merge_sort(input: Seq<int>) -> (output: Seq<int>)
    ensures(sort_spec(input, output))
{
}

pub fn merge(a: Seq<int>, b: Seq<int>) -> (output: Seq<int>)
    requires(is_sorted(a))
    requires(is_sorted(b))
    ensures(sort_spec(a.add(b), output))
{
}

pub fn fast_sort(input: Seq<int>) -> (output: Seq<int>)
{
}