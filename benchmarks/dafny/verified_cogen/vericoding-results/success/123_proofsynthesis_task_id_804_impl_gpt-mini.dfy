// <vc-preamble>
predicate IsEven(n: int)
{
    (n % 2) == 0
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): removed unnecessary null check and rely on arr being non-nullable */
lemma PrefixExistsImpliesFull(arr: array<int>, i: int)
  requires 0 <= i <= arr.Length
  ensures (exists k :: 0 <= k < i && IsEven(arr[k])) ==> (exists k :: 0 <= k < arr.Length && IsEven(arr[k]))
{ }

// </vc-helpers>

// <vc-spec>
method IsProductEven(arr: array<int>) returns (result: bool)
    ensures result <==> (exists k :: 0 <= k < arr.Length && IsEven(arr[k]))
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): implement linear scan with invariants to detect an even element */
  var i := 0;
  result := false;
  while i < arr.Length
    invariant 0 <= i <= arr.Length
    invariant (exists k :: 0 <= k < i && IsEven(arr[k])) <==> result
  {
    if IsEven(arr[i]) {
      result := true;
      return;
    }
    i := i + 1;
  }
}

// </vc-code>
