// <vc-preamble>
function IsPrime(n: nat) : bool
{
  n > 1 &&
  forall k :: 2 <= k < n ==> n % k != 0
}
function min(a: int, b: int): int
{
  if a <= b then a else b
}
function max(a: int, b: int): int
{
  if a >= b then a else b
}
// </vc-preamble>

// <vc-helpers>
function ComputeResult(start1: int, end1: int, start2: int, end2: int): string
{
  if max(start1, start2) <= min(end1, end2) && IsPrime((min(end1, end2) - max(start1, start2) + 1) as nat) then "YES" else "NO"
}
/* helper modified by LLM (iteration 2): fixed parameters to match Intersection method */
// </vc-helpers>

// <vc-spec>
method Intersection(start1: int, end1: int, start2: int, end2: int) returns (result: string)

  requires start1 <= end1 && start2 <= end2

  ensures result == "YES" || result == "NO"
  ensures result == "YES" <==>
    (max(start1, start2) <= min(end1, end2) &&
     IsPrime((min(end1, end2) - max(start1, start2) + 1) as nat))
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 3): use helper function */
  result := ComputeResult(start1, end1, start2, end2);
}
// </vc-code>
