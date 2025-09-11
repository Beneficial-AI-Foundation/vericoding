// <vc-preamble>
predicate ValidInput(coins: seq<int>)
{
  |coins| == 5 && forall i :: 0 <= i < |coins| ==> 0 <= coins[i] <= 100
}

function TotalCoins(coins: seq<int>): int
  requires |coins| == 5
{
  coins[0] + coins[1] + coins[2] + coins[3] + coins[4]
}

predicate HasValidSolution(coins: seq<int>)
  requires ValidInput(coins)
{
  var total := TotalCoins(coins);
  total > 0 && total % 5 == 0
}

function ComputeResult(coins: seq<int>): int
  requires ValidInput(coins)
{
  var total := TotalCoins(coins);
  if total > 0 && total % 5 == 0 then total / 5 else -1
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method solve(coins: seq<int>) returns (result: int)
  requires ValidInput(coins)
  ensures result == ComputeResult(coins)
  ensures HasValidSolution(coins) ==> result == TotalCoins(coins) / 5
  ensures !HasValidSolution(coins) ==> result == -1
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
