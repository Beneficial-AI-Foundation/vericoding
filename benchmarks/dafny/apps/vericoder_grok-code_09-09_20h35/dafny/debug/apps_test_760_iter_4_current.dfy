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
// No additional helpers needed
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
  var sequencer := s + seq(k, j => '*');
  var L := |sequencer|;
  var nn := if L % 2 == 0 then L else L - 1;
  result := 0;
  while nn >= 2
    invariant nn <= L
    invariant nn % 2 == 0
    invariant forall m :: nn < m <= L && m % 2 == 0 ==> !exists ii :: 0 <= ii <= L - m && is_tandem_repeat(sequencer[ii..ii+m])
    decreases nn
  {
    var found := false;
    var ii := 0;
    while ii <= L - nn && !found
      decreases L - nn - ii
    {
      if is_tandem_repeat(sequencer[ii..ii+nn]) {
        found := true;
      }
      ii := ii + 1;
    }
    if found {
      result := nn;
      break;
    }
    nn := nn - 2;
  }
}
// </vc-code>

