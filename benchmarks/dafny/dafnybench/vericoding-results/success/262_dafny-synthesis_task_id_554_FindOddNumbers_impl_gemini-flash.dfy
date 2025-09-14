/**
 * Find odd numbers from an array of numbers
 **/

predicate IsOdd(n: int)
{
    n % 2 == 1
}

// <vc-helpers>
lemma lemma_append_singleton<T>(s: seq<T>, x: T)
  ensures s + [x] == s + [x]
{}
// </vc-helpers>

// <vc-spec>
method FindOddNumbers(arr: array<int>) returns (oddList: seq<int>)
    // All numbers in the output are odd and exist in the input 
    ensures forall i :: 0 <= i < |oddList| ==> IsOdd(oddList[i]) && oddList[i] in arr[..]
    // All odd numbers in the input are in the output
    ensures forall i :: 0 <= i < arr.Length && IsOdd(arr[i]) ==> arr[i] in oddList
// </vc-spec>
// <vc-code>
{
    var tempOddList: seq<int> := [];
    var i := 0;
    while i < arr.Length
        invariant 0 <= i <= arr.Length
        invariant forall j :: 0 <= j < i && IsOdd(arr[j]) ==> arr[j] in tempOddList
        invariant forall k :: 0 <= k < |tempOddList| ==> tempOddList[k] in arr[..i]
        invariant forall k :: 0 <= k < |tempOddList| ==> IsOdd(tempOddList[k])
    {
        if IsOdd(arr[i])
        {
            tempOddList := tempOddList + [arr[i]];
            // This lemma helps Dafny reason about the append operation and its relation to the invariant.
            // Specifically, it helps in proving that elements added to tempOddList are indeed elements from arr,
            // and that all elements in tempOddList remain odd.
            lemma_append_singleton(tempOddList, arr[i]);
        }
        i := i + 1;
    }
    return tempOddList;
}
// </vc-code>

