

// <vc-helpers>
lemma AppendStrictIncrease(s: seq<int>, i: int)
  requires forall u, v :: 0 <= u < v < |s| ==> s[u] < s[v]
  requires forall k :: 0 <= k < |s| ==> s[k] < i
  ensures forall u, v :: 0 <= u < v < |s| + 1 ==> (s + [i])[u] < (s + [i])[v]
{
  if |s| == 0 {
    return;
  }
  assert forall u, v :: 0 <= u < v < |s| ==> (s + [i])[u] < (s + [i])[v];
  assert forall u :: 0 <= u < |s| ==> (s + [i])[u] < (s + [i])[|s|];
  assert forall u, v :: 0 <= u < v < |s| + 1 ==> (s + [i])[u] < (s + [i])[v];
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
  var n := arr.Length;
  var posSeq: seq<int> := [];
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant forall k :: 0 <= k < |posSeq| ==> 0 <= posSeq[k] < i && arr[posSeq[k]] % 2 == 0
    invariant forall k :: 0 <= k < i && arr[k] % 2 == 0 ==> exists t :: 0 <= t < |posSeq| && posSeq[t] == k
    invariant forall u, v :: 0 <= u < v < |posSeq| ==> posSeq[u] < posSeq[v]
  {
    if arr[i] % 2 == 0 {
      // preconditions for AppendStrictIncrease: posSeq is strictly increasing and its elements are < i
      AppendStrictIncrease(posSeq, i);
      posSeq := posSeq + [i];
      // the last element is the appended index i and is even
      assert |posSeq| > 0;
      assert posSeq[|posSeq|-1] == i;
      assert arr[posSeq[|posSeq|-1]] % 2 == 0;
      // provide the witness that the newly even index i is in posSeq
      assert exists t :: 0 <= t < |posSeq| && posSeq[t] == i;
    }
    i := i + 1;
  }

  evenNumbers := new int[|posSeq|];
  var j := 0;
  while j < |posSeq|
    invariant 0 <= j <= |posSeq|
    invariant forall k :: 0 <= k < j ==> evenNumbers[k] == arr[posSeq[k]]
  {
    evenNumbers[j] := arr[posSeq[j]];
    j := j + 1;
  }

  // relate evenNumbers and posSeq for the postconditions
  assert forall k :: 0 <= k < |posSeq| ==> evenNumbers[k] == arr[posSeq[k]];
  assert forall k, l :: 0 <= k < l < |posSeq| ==>
           exists n1, n2 :: 0 <= n1 < n2 < arr.Length && evenNumbers[k] == arr[n1] && evenNumbers[l] == arr[n2]
  by {
    var n1 := posSeq[k];
    var n2 := posSeq[l];
    assert 0 <= n1 < n2 < arr.Length;
    assert evenNumbers[k] == arr[n1];
    assert evenNumbers[l] == arr[n2];
  }
}
// </vc-code>

