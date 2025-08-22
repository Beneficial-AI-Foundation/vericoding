// SPEC

//lemma SequenceConcat(s:seq<int>, pivot:int)
// requires 0<=pivot<|s|
// ensures s[..pivot] + s[pivot..] == s
//{
}

method merge_sort(input:seq<int>) returns (output:seq<int>)
 ensures SortSpec(input, output)
{
}
