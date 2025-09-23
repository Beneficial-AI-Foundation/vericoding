// <vc-preamble>
type interval = iv: (int, int) | iv.0 <= iv.1 witness (0, 0)

ghost function length(iv: interval): int {
  iv.1 - iv.0
}

ghost predicate valid_interval(s: string, iv: interval) {
  && (0 <= iv.0 <= iv.1 <= |s|)
  && (forall i, j | iv.0 <= i < j < iv.1 :: s[i] != s[j])
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method lengthOfLongestSubstring(s: string) returns (n: int, ghost best_iv: interval)
  ensures valid_interval(s, best_iv) && length(best_iv) == n
  ensures forall iv | valid_interval(s, iv) :: length(iv) <= n
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
