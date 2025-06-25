// ATOM 
spec fn is_sorted(s: Seq<int>) -> bool
{
    forall|i: int| 0 <= i < s.len()-1 ==> s[i] <= s[i+1]
}

// ATOM 
spec fn sort_spec(input: Seq<int>, output: Seq<int>) -> bool
{
    && is_sorted(output)
    && output.to_multiset() == input.to_multiset()
}

// SPEC 
pub fn merge(a: Seq<int>, b: Seq<int>) -> (output: Seq<int>)
    requires(is_sorted(a))
    requires(is_sorted(b))
    ensures(sort_spec(a + b, output))
{
}

// SPEC 
pub fn merge(a: Seq<int>, b: Seq<int>) -> (output: Seq<int>)
    requires(is_sorted(a))
    requires(is_sorted(b))
    ensures(sort_spec(a + b, output))
{
}