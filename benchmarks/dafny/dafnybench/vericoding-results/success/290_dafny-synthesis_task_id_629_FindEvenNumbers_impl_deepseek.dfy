predicate IsEven(n: int)
{
    n % 2 == 0
}

// <vc-helpers>
lemma EvenInSeq(s: seq<int>, x: int)
  requires x in s && IsEven(x)
  ensures exists i :: 0 <= i < |s| && s[i] == x && IsEven(s[i])
{
}

lemma ForallInArrImpliesInSeq(arr: array<int>, s: seq<int>)
  requires forall i :: 0 <= i < arr.Length && IsEven(arr[i]) ==> arr[i] in s
  ensures forall i :: 0 <= i < arr.Length && IsEven(arr[i]) ==> exists j :: 0 <= j < |s| && s[j] == arr[i]
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
  evenList := [];
  var idx := 0;
  while idx < arr.Length
    invariant 0 <= idx <= arr.Length
    invariant forall i :: 0 <= i < |evenList| ==> IsEven(evenList[i]) && evenList[i] in arr[..]
    invariant forall i :: 0 <= i < idx && IsEven(arr[i]) ==> arr[i] in evenList
  {
    if IsEven(arr[idx]) {
      evenList := evenList + [arr[idx]];
    }
    idx := idx + 1;
  }
}
// </vc-code>

