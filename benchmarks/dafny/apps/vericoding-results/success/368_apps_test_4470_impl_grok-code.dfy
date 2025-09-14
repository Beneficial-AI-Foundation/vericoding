predicate ValidInput(n: nat)
{
    n > 0
}

predicate CanReachOne(n: nat)
    requires n > 0
{
    OnlyFactors235(n)
}

predicate OnlyFactors235(n: nat)
    requires n > 0
{
    ReduceByFactors235(n) == 1
}

function ReduceByFactors235(n: nat): nat
    requires n > 0
    decreases n
{
    if n == 1 then 1
    else if n % 2 == 0 then ReduceByFactors235(n / 2)
    else if n % 3 == 0 then ReduceByFactors235(n / 3)
    else if n % 5 == 0 then ReduceByFactors235(n / 5)
    else n
}

function MinMovesToOne(n: nat): nat
    requires n > 0
    requires CanReachOne(n)
    decreases n
{
    if n == 1 then 0
    else if n % 2 == 0 then 1 + MinMovesToOne(n / 2)
    else if n % 3 == 0 then 2 + MinMovesToOne(n / 3)
    else if n % 5 == 0 then 3 + MinMovesToOne(n / 5)
    else 0
}

// <vc-helpers>
// <vc-helpers>
method {:verify true} GetMinMoves(n: nat) returns (moves: int)
  requires ValidInput(n)
  decreases n
{
  if n == 1 {
    moves := 0;
  } else if n % 2 == 0 {
    var res := GetMinMoves(n / 2);
    moves := 1 + res;
  } else if n % 3 == 0 {
    var res := GetMinMoves(n / 3);
    moves := 2 + res;
  } else if n % 5 == 0 {
    var res := GetMinMoves(n / 5);
    moves := 3 + res;
  } else {
    moves := 0;
  }
}
// </vc-helpers>
// </vc-helpers>

// <vc-spec>
method Solve(n: nat) returns (result: int)
    requires ValidInput(n)
    ensures result >= -1
    ensures result == -1 <==> !CanReachOne(n)
    ensures result >= 0 ==> CanReachOne(n) && result == MinMovesToOne(n)
// </vc-spec>
// <vc-code>
{
  if ReduceByFactors235(n) != 1 {
    result := -1;
  } else {
    result := MinMovesToOne(n);
  }
}
// </vc-code>

