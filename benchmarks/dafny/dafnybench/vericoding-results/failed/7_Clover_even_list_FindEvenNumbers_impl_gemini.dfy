// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function GetEvens(s: seq<int>): seq<int>
{
  if s == [] then []
  else if s[0] % 2 == 0 then [s[0]] + GetEvens(s[1..])
  else GetEvens(s[1..])
}
// </vc-helpers>

// <vc-spec>
method FindEvenNumbers (arr: array<int>) returns (evenNumbers: array<int>)
  ensures forall x {:trigger (x%2) }:: x in arr[..] &&  (x%2==0)==> x in evenNumbers[..]
  ensures forall x :: x !in arr[..] ==> x !in evenNumbers[..]
  ensures forall k :: 0 <= k < evenNumbers.Length ==> evenNumbers[k] % 2 == 0
  ensures forall k, l :: 0 <= k < l < evenNumbers.Length ==>
                           exists n, m :: 0 <= n < m < arr.Length && evenNumbers[k] == arr[n] && evenNumbers[l] == arr[m]
// </vc-spec>
// <vc-code>
{
  var evens_seq : seq<int> := [];
  var i := 0;
  while i < arr.Length
    invariant 0 <= i <= arr.Length
    invariant evens_seq == GetEvens(arr[..i])
  {
    if arr[i] % 2 == 0 {
      evens_seq := evens_seq + [arr[i]];
    }
    i := i + 1;
  }

  evenNumbers := new int[|evens_seq|];
  var j := 0;
  while j < |evens_seq|
    invariant 0 <= j <= |evens_seq|
    invariant evens_seq == GetEvens(arr[..])
    invariant evenNumbers[..j] == evens_seq[..j]
  {
    evenNumbers[j] := evens_seq[j];
    j := j + 1;
  }
}
// </vc-code>
