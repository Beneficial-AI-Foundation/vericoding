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
lemma update_invariant(t: seq<char>, tLen: int, n_old: int)
  requires 2 <= n_old <= tLen
  requires n_old % 2 == 0
  requires forall i, m :: 0 <= i <= tLen - m && 2 <= m <= tLen && m % 2 == 0 && m > n_old ==> !is_tandem_repeat(t[i..i+m])
  requires forall j :: 0 <= j <= tLen - n_old ==> !is_tandem_repeat(t[j..j+n_old])
  ensures forall i, m :: 0 <= i <= tLen - m && 2 <= m <= tLen && m % 2 == 0 && m > n_old - 2 ==> !is_tandem_repeat(t[i..i+m])
{
  assert forall i, m :: 0 <= i <= tLen - m && 2 <= m <= tLen && m % 2 == 0 && m > n_old - 2 ==>
    !is_tandem_repeat(t[i..i+m])
  {
    if m > n_old {
      // covered by the first precondition
      assert !is_tandem_repeat(t[i..i+m]);
    } else {
      // m <= n_old and m > n_old - 2, with both even implies m == n_old
      assert m == n_old;
      assert 0 <= i <= tLen - n_old;
      // covered by the second precondition
      assert !is_tandem_repeat(t[i..i+n_old]);
    }
  }
}
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
    // At this point, i > limit and invariant gives i <= limit + 1, so i == limit + 1.
    assert i > limit;
    assert i <= limit + 1;
    assert i == limit + 1;

    // From inner-loop invariant we get there is no tandem repeat of length n at any start.
    assert forall j :: 0 <= j <= tLen - n ==> !is_tandem_repeat(t[j..j+n])
    {
      // j is arbitrary in the quantifier's scope
      assert j <= limit;
      assert j < i;
      assert !is_tandem_repeat(t[j..j+n]);
    }

    // Use lemma to extend the outer invariant for the next smaller even n.
    update_invariant(t, tLen, n);

    // Decrease n by 2 and continue searching smaller even lengths.
    n := n - 2;
  }
  return 0;
}
// </vc-code>

