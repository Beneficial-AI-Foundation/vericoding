//ATOM_PLACEHOLDER_IsSorted

//ATOM_PLACEHOLDER_SortSpec

//lemma SequenceConcat(s:seq<int>, pivot:int)
//  requires 0<=pivot<|s|
//  ensures s[..pivot] + s[pivot..] == s
//{
//}

// SPEC 

//lemma SequenceConcat(s:seq<int>, pivot:int)
//  requires 0<=pivot<|s|
//  ensures s[..pivot] + s[pivot..] == s
//{
}

method merge_sort(input:seq<int>) returns (output:seq<int>)
  ensures SortSpec(input, output)
{
}


//ATOM_PLACEHOLDER_merge

//ATOM_PLACEHOLDER_fast_sort



