// <vc-preamble>
predicate ValidInput(input: seq<seq<int>>)
{
    |input| > 0 &&
    |input| <= 1000000 &&
    (forall i :: 0 <= i < |input| ==> |input[i]| > 0) &&
    (forall i :: 0 <= i < |input| ==> input[i][0] == |input[i]| - 1) &&
    (forall i :: 0 <= i < |input| ==> input[i][0] >= 1) &&
    (forall i :: 0 <= i < |input| ==> forall j :: 1 <= j < |input[i]| ==> 1 <= input[i][j] <= 1000000) &&
    (forall i :: 0 <= i < |input| ==> forall j1, j2 :: 1 <= j1 < j2 < |input[i]| ==> input[i][j1] != input[i][j2]) &&
    SumOfDesiredItems(input) <= 1000000
}

function SumOfDesiredItems(input: seq<seq<int>>): int
    requires forall i :: 0 <= i < |input| ==> |input[i]| > 0
    requires forall i :: 0 <= i < |input| ==> input[i][0] == |input[i]| - 1
{
    if |input| == 0 then 0 else input[0][0] + SumOfDesiredItems(input[1..])
}

predicate ValidOutput(result: int)
{
    0 <= result < 998244353
}
// </vc-preamble>

// <vc-helpers>
function ModPow(base: int, exp: int, mod: int): int
    requires exp >= 0
    requires mod > 0
    decreases exp
{
    if exp == 0 then 1
    else if exp % 2 == 0 then
        var half := ModPow(base, exp / 2, mod);
        (half * half) % mod
    else
        (base * ModPow(base, exp - 1, mod)) % mod
}
// </vc-helpers>

// <vc-spec>
method solve(input: seq<seq<int>>) returns (result: int)
    requires ValidInput(input)
    ensures ValidOutput(result)
// </vc-spec>
// <vc-code>
{
    var n := |input|;
    var MOD := 998244353;

    // Parse input - skip first element of each row (which is k_i)
    var wants: seq<seq<int>> := [];
    for i := 0 to n 
        invariant 0 <= i <= n
        invariant |wants| == i
        invariant forall k :: 0 <= k < i ==> wants[k] == input[k][1..]
    {
        if |input[i]| > 1 {
            wants := wants + [input[i][1..]];
        } else {
            wants := wants + [[]];
        }
    }

    // Initialize arrays for items 0 to 1000000
    var MAX_ITEM := 1000000;
    var tmpCall1 := seq(MAX_ITEM + 1, i => 0);
    var P: seq<int> := tmpCall1;
    var tmpCall2 := seq(MAX_ITEM + 1, i => 0);
    var Q: seq<int> := tmpCall2;

    // Process each kid
    for i := 0 to n 
        invariant 0 <= i <= n
        invariant |P| == MAX_ITEM + 1
        invariant |Q| == MAX_ITEM + 1
    {
        var k := |wants[i]|;
        if k > 0 {
            var kinv := ModPow(k, MOD - 2, MOD);
            for j := 0 to k 
                invariant 0 <= j <= k
                invariant |P| == MAX_ITEM + 1
                invariant |Q| == MAX_ITEM + 1
            {
                var w := wants[i][j];
                if 0 <= w <= MAX_ITEM {
                    P := P[w := P[w] + 1];
                    Q := Q[w := (Q[w] + kinv) % MOD];
                }
            }
        }
    }

    // Calculate result
    var res := 0;
    for i := 0 to MAX_ITEM + 1 
        invariant 0 <= i <= MAX_ITEM + 1
        invariant |P| == MAX_ITEM + 1
        invariant |Q| == MAX_ITEM + 1
    {
        res := (res + (P[i] * Q[i]) % MOD) % MOD;
    }

    var n_squared := (n * n) % MOD;
    var n_squared_inv := ModPow(n_squared, MOD - 2, MOD);
    result := (n_squared_inv * res) % MOD;
}
// </vc-code>
