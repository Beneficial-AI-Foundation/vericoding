// sums from index 0 -> i - 1
function sumcheck(s: array<int>, i: int): int
requires 0 <= i <= s.Length
reads s
{
    if i == 0 then 0
    else s[i - 1] + sumcheck(s, i - 1)
}

// returns sum of array

// <vc-helpers>
lemma sumcheck_loop_invariant(s: array<int>, i: int, current_sum: int)
requires 0 <= i <= s.Length
requires current_sum == sumcheck(s, i)
ensures current_sum == sumcheck(s, i)
{
}

lemma sumcheck_step(s: array<int>, i: int)
requires 0 <= i < s.Length
ensures sumcheck(s, i + 1) == s[i] + sumcheck(s, i)
{
}
// </vc-helpers>

// <vc-spec>
method sum(s: array<int>) returns (a:int)
requires s.Length > 0
ensures sumcheck(s, s.Length) == a
// </vc-spec>
// <vc-code>
{
  a := 0;
  var i := 0;
  
  while i < s.Length
  invariant 0 <= i <= s.Length
  invariant a == sumcheck(s, i)
  {
    sumcheck_step(s, i);
    a := a + s[i];
    i := i + 1;
  }
}
// </vc-code>

