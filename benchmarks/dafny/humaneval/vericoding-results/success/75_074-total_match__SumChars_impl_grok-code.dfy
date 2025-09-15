// <vc-preamble>
function sum_chars_rec(list: seq<string>): nat
{
  if |list| == 0 then 0
  else |list[0]| + sum_chars_rec(list[1..])
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method SumChars(list: seq<string>) returns (sum: nat)

  ensures sum == sum_chars_rec(list)
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 3): Changed to while loop from end with proper invariant */
  var s: nat := 0;
  var i: int := |list|;
  while i > 0
    invariant 0 <= i <= |list|
    invariant s == sum_chars_rec(list[i..])
  {
    i := i - 1;
    s := s + |list[i]|;
  }
  sum := s;
}
// </vc-code>
