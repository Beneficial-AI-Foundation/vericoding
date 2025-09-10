function is_tandem_repeat(s: seq<char>): bool
{
    if |s| % 2 != 0 then false
    else
        var half_len := |s| / 2;
        var first_half := s[0..half_len];
        var second_half := s[half_len..];
        forall i :: 0 <= i < half_len ==> 
            (first_half[i] == '*' || second_half[i] == '*' || first_half[i] == second_half[i])
}

// <vc-helpers>
// No helper lemmas required for this implementation.
// </vc-helpers>

// <vc-spec>
method solve(s: string, k: int) returns (result: int)
    requires k >= 1
    requires |s| >= 1
    ensures result >= 0
    ensures result % 2 == 0
    ensures result <= |s| + k
    ensures forall i, n :: 0 <= i < |s| + k && 2 <= n <= |s| + k - i && n % 2 == 0 && 
            is_tandem_repeat((s + seq(k, j => '*'))[i..i+n]) ==> n <= result
    ensures result == 0 ==> forall i, n :: 0 <= i < |s| + k && 2 <= n <= |s| + k - i && n % 2 == 0 ==> 
            !is_tandem_repeat((s + seq(k, j => '*'))[i..i+n])
    ensures result > 0 ==> exists i, n :: 0 <= i < |s| + k && 2 <= n <= |s| + k - i && n % 2 == 0 && 
            (is_tandem_repeat((s + seq(k, j => '*'))[i..i+n]) && n == result)
// </vc-spec>
// <vc-code>
{
  var t := s + seq(k, j => '*');
  var tLen := |t|;
  var n := if tLen % 2 == 0 then tLen else tLen - 1;
  while n >= 2
    decreases n
    invariant 0 <= n <= tLen
    invariant n % 2 == 0
    invariant forall i, m :: 0 <= i <= tLen - m && 2 <= m <= tLen && m % 2 == 0 && m > n ==> !is_tandem_repeat(t[i..i+m])
  {
    var limit := tLen - n;
    var i := 0;
    while i <= limit
      decreases limit - i
      invariant 0 <= i <= limit + 1
      invariant forall j :: 0 <= j < i ==> !is_tandem_repeat(t[j..j+n])
    {
      if is_tandem_repeat(t[i..i+n]) {
        return n;
      }
      i := i + 1;
    }
    // At this point, no substring of length n is a tandem repeat.
    // Decrease n by 2 and continue searching smaller even lengths.
    n := n - 2;
  }
  return 0;
}
// </vc-code>

