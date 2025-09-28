// <vc-preamble>
predicate IsEven(n: int)
{
    n % 2 == 0
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): define transparent counting function over array prefix */
function CountEvensPrefix(arr: array<int>, n: nat): nat
    requires n <= arr.Length
    reads arr
{
    if n == 0 then 0 else CountEvensPrefix(arr, n - 1) + (if IsEven(arr[n - 1]) then 1 else 0)
}

/* helper modified by LLM (iteration 3): unfolding lemma for CountEvensPrefix */
lemma CountEvensPrefix_Unfold(arr: array<int>, n: nat)
    requires n <= arr.Length
    ensures n == 0 ==> CountEvensPrefix(arr, n) == 0
    ensures 0 < n ==> CountEvensPrefix(arr, n) == CountEvensPrefix(arr, n - 1) + (if IsEven(arr[n - 1]) then 1 else 0)
{
    reveal CountEvensPrefix();
}

/* helper modified by LLM (iteration 3): monotonicity of CountEvensPrefix over n */
lemma CountEvensPrefix_Monotonic(arr: array<int>, n1: nat, n2: nat)
    requires n1 <= n2 <= arr.Length
    ensures CountEvensPrefix(arr, n1) <= CountEvensPrefix(arr, n2)
    decreases n2 - n1
{
    if n1 < n2 {
        CountEvensPrefix_Monotonic(arr, n1, n2 - 1);
        CountEvensPrefix_Unfold(arr, n2);
        assert 0 <= (if IsEven(arr[n2 - 1]) then 1 else 0);
        assert CountEvensPrefix(arr, n2 - 1) <= CountEvensPrefix(arr, n2);
        assert CountEvensPrefix(arr, n1) <= CountEvensPrefix(arr, n2 - 1);
        assert CountEvensPrefix(arr, n1) <= CountEvensPrefix(arr, n2);
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
  /* code modified by LLM (iteration 3): two-pass extraction using prefix-count helpers and unfolding lemma */
  var count: nat := 0;
  var i: nat := 0;
  while i < arr.Length
    invariant 0 <= i <= arr.Length
    invariant count == CountEvensPrefix(arr, i)
    decreases arr.Length - i
  {
    CountEvensPrefix_Unfold(arr, i + 1);
    if IsEven(arr[i]) {
      count := count + 1;
    }
    i := i + 1;
  }
  result := new int[count];
  var j: nat := 0;
  i := 0;
  while i < arr.Length
    invariant 0 <= i <= arr.Length
    invariant j == CountEvensPrefix(arr, i)
    invariant 0 <= j <= result.Length
    invariant forall k :: 0 <= k < j ==> IsEven(result[k])
    invariant forall k :: 0 <= k < j ==> exists r :: 0 <= r < i && result[k] == arr[r]
    decreases arr.Length - i
  {
    if IsEven(arr[i]) {
      CountEvensPrefix_Unfold(arr, i + 1);
      assert CountEvensPrefix(arr, i + 1) == CountEvensPrefix(arr, i) + 1;
      CountEvensPrefix_Monotonic(arr, i + 1, arr.Length);
      assert CountEvensPrefix(arr, i + 1) <= CountEvensPrefix(arr, arr.Length);
      assert j == CountEvensPrefix(arr, i);
      assert j + 1 == CountEvensPrefix(arr, i + 1);
      assert CountEvensPrefix(arr, arr.Length) == count;
      assert j + 1 <= result.Length;
      result[j] := arr[i];
      j := j + 1;
    }
    i := i + 1;
  }
}
// </vc-code>
