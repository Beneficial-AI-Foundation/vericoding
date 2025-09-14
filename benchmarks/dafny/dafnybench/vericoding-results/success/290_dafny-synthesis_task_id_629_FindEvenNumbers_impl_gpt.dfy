predicate IsEven(n: int)
{
    n % 2 == 0
}

// <vc-helpers>

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
  var s: seq<int> := [];
  var i := 0;
  while i < arr.Length
    invariant 0 <= i <= arr.Length
    invariant forall j :: 0 <= j < i && IsEven(arr[j]) ==> arr[j] in s
    invariant forall k :: 0 <= k < |s| ==> s[k] in arr[..i] && IsEven(s[k])
    decreases arr.Length - i
  {
    if IsEven(arr[i]) {
      s := s + [arr[i]];
    }
    i := i + 1;
    if 0 < i {
      assert arr[i - 1] in arr[..i];
    }
  }
  evenList := s;
}
// </vc-code>

