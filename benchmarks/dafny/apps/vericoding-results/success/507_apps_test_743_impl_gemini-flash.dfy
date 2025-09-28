// <vc-preamble>
predicate ValidInput(n: int, ar: seq<int>)
{
  n >= 2 && |ar| == n && forall i :: 0 <= i < n ==> ar[i] > 0
}

function GCD(x: int, y: int): int
  requires x > 0 && y > 0
  ensures GCD(x, y) > 0
  decreases if x < y then y else x
{
  if x == y then x
  else if x < y then GCD(x, y - x)
  else GCD(x - y, y)
}

function GCDOfSequence(ar: seq<int>): int
  requires |ar| >= 1
  requires forall i :: 0 <= i < |ar| ==> ar[i] > 0
  ensures GCDOfSequence(ar) > 0
  decreases |ar|
{
  if |ar| == 1 then ar[0]
  else GCD(ar[0], GCDOfSequence(ar[1..]))
}

function MinimalSum(n: int, ar: seq<int>): int
  requires ValidInput(n, ar)
{
  GCDOfSequence(ar) * n
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): The original `FindGCD` helper was already correct in logic but `GCDOfSequence` already exists. No modification needed, leaving as is. */
function FindGCD(s: seq<int>): int
  requires |s| >= 1
  requires forall i :: 0 <= i < |s| ==> s[i] > 0
  ensures FindGCD(s) > 0
  decreases |s|
{
  if |s| == 1 then s[0]
  else GCD(s[0], FindGCD(s[1..]))
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, ar: seq<int>) returns (result: int)
  requires ValidInput(n, ar)
  ensures result == MinimalSum(n, ar)
  ensures result > 0
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): replaced `FindGCD` with the already existing and verified `GCDOfSequence` to directly leverage the `MinimalSum` function definition. */
{
  result := GCDOfSequence(ar) * n;
}
// </vc-code>
