// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method myfun(a: array<int>, sum: array<int>, N: int)
	requires
		N > 0 &&
		a.Length == N &&
		sum.Length == 1 &&
		N < 1000
	ensures
		sum[0] == 2 * N
	modifies a, sum
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 3): [Separated the logic into two steps to resolve a loop invariant violation caused by potential aliasing. First, a loop correctly initializes array 'a'. Second, 'sum[0]' is assigned the final value directly. This avoids modifying 'sum' within the loop, which could have invalidated the invariant on 'a'.] */
  var i: int := 0;
  while i < N
    invariant 0 <= i <= N
    invariant forall k :: 0 <= k < i ==> a[k] == 2
    modifies a
  {
    a[i] := 2;
    i := i + 1;
  }
  sum[0] := 2 * N;
}
// </vc-code>
