// <vc-preamble>
predicate IsEven(n: int)
{
    n % 2 == 0
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): recursive filter to collect even numbers preserving order */
function FilterEven(s: seq<int>): seq<int>
  ensures forall x :: x in result ==> x in s && IsEven(x)
  ensures forall x :: x in s && IsEven(x) ==> x in result
  ensures forall i, j :: 0 <= i < |s| && 0 <= j < |s| && i <= j && IsEven(s[i]) && IsEven(s[j]) ==>
            exists ri, rj :: 0 <= ri < |result| && 0 <= rj < |result| && ri <= rj && result[ri] == s[i] && result[rj] == s[j]
  decreases s
{
  if |s| == 0 then []
  else if IsEven(s[0]) then [s[0]] + FilterEven(s[1..])
  else FilterEven(s[1..])
}

// </vc-helpers>

// <vc-spec>
method FindEvenNumbers(arr: array<int>) returns (result: array<int>)
    ensures forall x :: x in result[..] ==> IsEven(x) && x in arr[..]
    ensures forall x :: x in arr[..] && IsEven(x) ==> x in result[..]
    ensures forall i, j :: 0 <= i < arr.Length && 0 <= j < arr.Length && i <= j 
        && IsEven(arr[i]) && IsEven(arr[j]) ==> 
        exists ri, rj :: 0 <= ri < result.Length && 0 <= rj < result.Length 
            && ri <= rj && result[ri] == arr[i] && result[rj] == arr[j]
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): filter array to sequence of evens and copy into result array */
{
  var evens := FilterEven(arr[..]);
  result := new int[|evens|];
  var i := 0;
  while i < |evens|
    invariant 0 <= i <= |evens|
    invariant result.Length == |evens|
    invariant forall k :: 0 <= k < i ==> result[k] == evens[k]
  {
    result[i] := evens[i];
    i := i + 1;
  }
}

// </vc-code>
