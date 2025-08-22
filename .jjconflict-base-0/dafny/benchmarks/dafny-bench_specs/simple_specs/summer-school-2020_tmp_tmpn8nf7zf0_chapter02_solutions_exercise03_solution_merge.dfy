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

method merge(a:seq<int>, b:seq<int>) returns (output:seq<int>)
 requires IsSorted(a)
 requires IsSorted(b)
// ensures IsSorted(output)
 ensures SortSpec(a+b, output)
 //decreases |a|+|b|
{
}
