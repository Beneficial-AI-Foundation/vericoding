// <vc-preamble>
predicate IsEven(n: int)
{
    n % 2 == 0
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): count evens in prefix of sequence */
function CountEvensPrefix(s: seq<int>, n: nat): nat
  requires n <= |s|
{
  if n == 0 then 0 else CountEvensPrefix(s, n-1) + (if IsEven(s[n-1]) then 1 else 0)
}

/* helper modified by LLM (iteration 3): monotonicity of CountEvensPrefix */
lemma MonotoneCount(s: seq<int>, n: nat, m: nat)
  requires n <= m <= |s|
  decreases m - n
  ensures CountEvensPrefix(s,n) <= CountEvensPrefix(s,m)
{
  if n < m {
    MonotoneCount(s, n, m-1);
    assert CountEvensPrefix(s,m) == CountEvensPrefix(s,m-1) + (if IsEven(s[m-1]) then 1 else 0);
    assert CountEvensPrefix(s,m-1) <= CountEvensPrefix(s,m);
  }
}

/* helper modified by LLM (iteration 3): if element at i is even, total count is larger */
lemma CountIncreaseIfEven(s: seq<int>, i: nat)
  requires i < |s|
  requires IsEven(s[i])
  decreases |s| - i
  ensures CountEvensPrefix(s,i) < CountEvensPrefix(s,|s|)
{
  if i+1 == |s| {
    // last element
    assert CountEvensPrefix(s,|s|) == CountEvensPrefix(s,|s|-1) + (if IsEven(s[|s|-1]) then 1 else 0);
    assert CountEvensPrefix(s,|s|) == CountEvensPrefix(s,i) + 1;
  } else {
    assert CountEvensPrefix(s,i+1) == CountEvensPrefix(s,i) + (if IsEven(s[i]) then 1 else 0);
    assert CountEvensPrefix(s,i+1) == CountEvensPrefix(s,i) + 1;
    MonotoneCount(s, i+1, |s|);
    assert CountEvensPrefix(s,i+1) <= CountEvensPrefix(s,|s|);
    assert CountEvensPrefix(s,i) < CountEvensPrefix(s,|s|);
  }
}
// </vc-helpers>

// <vc-spec>
method FindEvenNumbers(arr: array<int>) returns (result: array<int>)
    ensures forall i :: 0 <= i < result.Length ==> IsEven(result[i])
    ensures forall i :: 0 <= i < result.Length ==> exists j :: 0 <= j < arr.Length && result[i] == arr[j]
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 3): compute and collect even numbers with lemmas to ensure safe indexing */
  var s := arr[..];
  var cnt := CountEvensPrefix(s, |s|);
  result := new int[cnt];
  var idx := 0;
  var i := 0;
  while i < arr.Length
    invariant 0 <= i <= arr.Length
    invariant 0 <= idx <= cnt
    invariant idx == CountEvensPrefix(s, i)
    invariant forall k :: 0 <= k < idx ==> IsEven(result[k])
    invariant forall k :: 0 <= k < idx ==> exists j :: 0 <= j < i && result[k] == arr[j]
    decreases arr.Length - i
  {
    if IsEven(arr[i]) {
      CountIncreaseIfEven(s, i);
      assert idx < cnt;
      result[idx] := arr[i];
      idx := idx + 1;
    }
    i := i + 1;
  }
  assert idx == cnt;
  return;
}
// </vc-code>
