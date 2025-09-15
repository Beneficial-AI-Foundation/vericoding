// <vc-preamble>
function sum_chars_rec(list: seq<string>): nat
{
  if |list| == 0 then 0
  else |list[0]| + sum_chars_rec(list[1..])
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): prove base case for sum_chars_rec on empty sequence */
lemma SumEmpty()
  ensures sum_chars_rec([]) == 0
{ }
// </vc-helpers>

// <vc-spec>
method SumChars(list: seq<string>) returns (sum: nat)

  ensures sum == sum_chars_rec(list)
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): compute the sum using the recursive helper function */
  sum := sum_chars_rec(list);
}
// </vc-code>
