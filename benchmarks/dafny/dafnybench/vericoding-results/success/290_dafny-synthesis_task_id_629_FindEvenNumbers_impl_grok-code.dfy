predicate IsEven(n: int)
{
    n % 2 == 0
}

// <vc-helpers>
// Helper code or proofs if needed (empty for this implementation)
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
  var result: seq<int> := [];
  var i: int := 0;
  while i < arr.Length
    invariant 0 <= i <= arr.Length
    invariant forall k :: 0 <= k < i ==> (IsEven(arr[k]) ==> arr[k] in result)
    invariant forall el :: el in result ==> IsEven(el) && el in arr[..i]
  {
    if IsEven(arr[i]) {
      result := result + [arr[i]];
    }
    i := i + 1;
  }
  evenList := result;
}
// </vc-code>

