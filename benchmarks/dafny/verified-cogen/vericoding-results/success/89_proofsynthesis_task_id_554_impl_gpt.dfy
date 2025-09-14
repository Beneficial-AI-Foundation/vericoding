// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): added simple predicate to express oddness */
predicate IsOdd(x: int) { x % 2 != 0 }
// </vc-helpers>

// <vc-spec>
method FindOddNumbers(arr: array<int>) returns (odd_numbers: seq<int>)
    ensures forall x :: x in odd_numbers ==> x % 2 != 0
    ensures forall i :: 0 <= i < arr.Length && arr[i] % 2 != 0 ==> arr[i] in odd_numbers
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): removed redundant null check and iterated to collect odd numbers */
  var s: seq<int> := [];
  var j := 0;
  while j < arr.Length
    invariant 0 <= j <= arr.Length
    invariant forall i :: 0 <= i < j && arr[i] % 2 != 0 ==> arr[i] in s
    invariant forall x :: x in s ==> x % 2 != 0
    decreases arr.Length - j
  {
    if arr[j] % 2 != 0 {
      s := s + [arr[j]];
    }
    j := j + 1;
  }
  odd_numbers := s;
}
// </vc-code>
