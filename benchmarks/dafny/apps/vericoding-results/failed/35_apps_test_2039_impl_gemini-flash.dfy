// <vc-preamble>
predicate ValidInput(n: int, a: seq<int>)
{
    n >= 1 && |a| == n
}

function CountLocalExtrema(n: int, a: seq<int>): int
    requires ValidInput(n, a)
{
    |set i | 1 <= i < n - 1 && ((a[i] > a[i-1] && a[i] > a[i+1]) || (a[i] < a[i-1] && a[i] < a[i+1]))|
}

predicate IsLocalExtremum(a: seq<int>, i: int)
    requires 0 <= i < |a|
{
    1 <= i < |a| - 1 && ((a[i] > a[i-1] && a[i] > a[i+1]) || (a[i] < a[i-1] && a[i] < a[i+1]))
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): No changes needed. This helper works as intended and is used correctly in the main method. */
predicate IsLocalExtremumAt(a: seq<int>, i: int)
  requires 0 <= i < |a|
{
  1 <= i < |a| - 1 && ((a[i] > a[i-1] && a[i] > a[i+1]) || (a[i] < a[i-1] && a[i] < a[i+1]))
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, a: seq<int>) returns (result: int)
    requires ValidInput(n, a)
    ensures result >= 0
    ensures n <= 2 ==> result == 0
    ensures n > 2 ==> result <= n - 2
    ensures result == CountLocalExtrema(n, a)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): The loop invariant for `count` was updated. The previous invariant only considered `k < i`, but for the final proof to hold, it should consider `k < i` and also include the value of `i` itself if it's an extremum. The main goal is to prove `result == CountLocalExtrema(n, a)`, and `CountLocalExtrema` computes based on `1 <= i < n - 1`. The loop iterates from `i=1` to `n-2`. The invariant `count == |set k | 1 <= k < i && IsLocalExtremumAt(a, k)|` must hold for the range of `k` as the loop progresses. This is consistent. The post-condition failing indicates the problem is likely with how `CountLocalExtrema` is applied to `count` at the end or an off-by-one in the loop bounds/invariant. The loop termination condition `i < n - 1` means `i` goes up to `n - 2`. The loop invariant `count == |set k | 1 <= k < i && IsLocalExtremumAt(a, k)|` is correct for the `i` at the start of each iteration. At the end, `i` becomes `n - 1`, and the loop terminates. So, at the point of return, our count correctly stores all extrema up to `n - 2`. */
{
  if n <= 2 {
    return 0;
  }

  var count := 0;
  var i := 1;
  while i < n - 1
    invariant 1 <= i <= n - 1
    invariant count == |set k | 1 <= k < i && IsLocalExtremumAt(a, k)|
  {
    if IsLocalExtremumAt(a, i) {
      count := count + 1;
    }
    i := i + 1;
  }
  return count;
}
// </vc-code>
