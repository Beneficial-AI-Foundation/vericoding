// <vc-preamble>
function first_digit(n: int): int
  requires n >= 0
  ensures 0 <= first_digit(n) < 10
{
  if n < 10 then n else first_digit(n / 10)
}
function last_digit(n: int): int
  requires n >= 0
  ensures 0 <= last_digit(n) < 10
  ensures last_digit(n) == n % 10
{
  n % 10
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): Changed predicate to function to enable calling and use of asserts for better verification of postconditions. */
function Satisfies(x: int): bool requires x >= 0
  ensures Satisfies(x) ==> x > 10 && first_digit(x) % 2 == 1 && last_digit(x) % 2 == 1
{ x > 10 && first_digit(x) % 2 == 1 && last_digit(x) % 2 == 1 }
// </vc-helpers>

// <vc-spec>
method specialFilter(s: seq<int>) returns (r: seq<int>)

  ensures forall i :: 0 <= i < |r| ==> r[i] > 10
  ensures forall x :: x in r ==> x in s
  ensures forall i :: 0 <= i < |r| ==> first_digit(r[i]) % 2 == 1 && last_digit(r[i]) % 2 == 1
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 5): Fixed for loop range to prevent lower bound exceeding upper bound when sequence is empty. */
  r := [];
  for i := 0 to |s|
    invariant |r| <= i
    invariant forall k :: 0 <= k < |r| ==> r[k] in s
    invariant forall k :: 0 <= k < |r| ==> r[k] > 10
    invariant forall k :: 0 <= k < |r| ==> first_digit(r[k]) % 2 == 1 && last_digit(r[k]) % 2 == 1
  {
    if s[i] >= 0 && Satisfies(s[i]) {
      assert s[i] > 10;
      assert first_digit(s[i]) % 2 == 1;
      assert last_digit(s[i]) % 2 == 1;
      r := r + [s[i]];
    }
  }
}
// </vc-code>
