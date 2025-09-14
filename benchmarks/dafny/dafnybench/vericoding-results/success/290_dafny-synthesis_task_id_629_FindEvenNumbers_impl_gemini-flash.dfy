predicate IsEven(n: int)
{
    n % 2 == 0
}

// <vc-helpers>
lemma lemma_append_seq_contains_element<T>(s: seq<T>, x: T)
  ensures x in s + [x]
{
}
// </vc-helpers>

// <vc-spec>
method FindEvenNumbers(arr: array<int>) returns (evenList: seq<int>)
    // All numbers in the output are even and exist in the input 
    ensures forall i :: 0 <= i < |evenList| ==> IsEven(evenList[i]) && evenList[i] in arr[..]
    // All even numbers in the input are in the output
    ensures forall i :: 0 <= i < arr.Length && IsEven(arr[i]) ==> arr[i] in evenList
// </vc-spec>
// <vc-code>
{
    var evenList_local: seq<int> := [];
    var i := 0;
    while i < arr.Length
        invariant 0 <= i <= arr.Length
        invariant forall j :: 0 <= j < |evenList_local| ==> IsEven(evenList_local[j]) && evenList_local[j] in arr[..]
        invariant forall k :: 0 <= k < i && IsEven(arr[k]) ==> arr[k] in evenList_local
    {
        if IsEven(arr[i]) {
            evenList_local := evenList_local + [arr[i]];
            lemma_append_seq_contains_element(evenList_local, arr[i]); // Prove arr[i] is now in evenList
        }
        i := i + 1;
    }
    return evenList_local;
}
// </vc-code>

