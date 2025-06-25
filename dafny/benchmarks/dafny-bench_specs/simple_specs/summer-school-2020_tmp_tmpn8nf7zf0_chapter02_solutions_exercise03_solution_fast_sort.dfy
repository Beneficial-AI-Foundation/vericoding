//ATOM
predicate IsSorted(s:seq<int>)
{
 forall i :: 0 <= i < |s|-1 ==> s[i] <= s[i+1]
}


//ATOM

predicate SortSpec(input:seq<int>, output:seq<int>)
{
 && IsSorted(output)
 && multiset(output) == multiset(input)
}


// SPEC

method fast_sort(input:seq<int>) returns (output:seq<int>)
// ensures SortSpec(input, output)
{
}
