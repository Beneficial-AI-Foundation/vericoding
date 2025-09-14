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
// no helpers needed
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
  var nMax := 0;
  var wI := 0;
  var wN := 0;

  var i := 0;
  while i < tLen
    invariant 0 <= i <= tLen
    invariant nMax % 2 == 0
    invariant 0 <= nMax <= tLen
    invariant (nMax == 0) || (0 <= wI < tLen && 2 <= wN <= tLen - wI && wN % 2 == 0 && is_tandem_repeat(t[wI..wI+wN]) && wN == nMax)
    invariant forall ii, nn {:trigger is_tandem_repeat(t[ii..ii+nn])} ::
               0 <= ii < i && 2 <= nn <= tLen - ii && nn % 2 == 0 && is_tandem_repeat(t[ii..ii+nn]) ==> nn <= nMax
    decreases tLen - i
  {
    var n := 2;
    while n <= tLen - i
      invariant 2 <= n <= tLen - i + 2
      invariant n % 2 == 0
      invariant nMax % 2 == 0
      invariant 0 <= nMax <= tLen
      invariant (nMax == 0) || (0 <= wI < tLen && 2 <= wN <= tLen - wI && wN % 2 == 0 && is_tandem_repeat(t[wI..wI+wN]) && wN == nMax)
      invariant forall nn {:trigger is_tandem_repeat(t[i..i+nn])} ::
                 2 <= nn < n && nn % 2 == 0 && is_tandem_repeat(t[i..i+nn]) ==> nn <= nMax
      invariant forall ii, nn {:trigger is_tandem_repeat(t[ii..ii+nn])} ::
                 0 <= ii < i && 2 <= nn <= tLen - ii && nn % 2 == 0 && is_tandem_repeat(t[ii..ii+nn]) ==> nn <= nMax
      decreases tLen - i - n
    {
      if is_tandem_repeat(t[i..i+n]) && nMax < n {
        nMax := n;
        wI := i;
        wN := n;
      }
      n := n + 2;
    }
    i := i + 1;
  }
  result := nMax;
}
// </vc-code>

