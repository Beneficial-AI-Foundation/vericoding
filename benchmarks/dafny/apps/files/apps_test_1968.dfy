Given n sellers and Valera's budget v, determine which sellers Valera can make a deal with.
Each seller i has ki items with prices. Valera can buy from seller i if his budget v is
strictly greater than the minimum price among seller i's items.

predicate ValidInput(n: int, v: int, sellers: seq<seq<int>>) {
    n >= 0 && v >= 0 && |sellers| == n && 
    forall i :: 0 <= i < |sellers| ==> |sellers[i]| > 0
}

predicate ValidOutput(count: int, indices: seq<int>, n: int) {
    count == |indices| && count >= 0 && count <= n &&
    (forall i :: 0 <= i < |indices| ==> 1 <= indices[i] <= n) &&
    (forall i :: 0 <= i < |indices| - 1 ==> indices[i] < indices[i+1])
}

predicate CorrectSolution(v: int, sellers: seq<seq<int>>, indices: seq<int>) 
    requires forall i :: 0 <= i < |sellers| ==> |sellers[i]| > 0
    requires forall i :: 0 <= i < |indices| ==> 1 <= indices[i] <= |sellers|
{
    (forall i :: 0 <= i < |indices| ==> v > Min(sellers[indices[i] - 1])) &&
    (forall i :: 0 <= i < |sellers| ==> (v > Min(sellers[i]) <==> (i + 1) in indices))
}

function Min(prices: seq<int>): int
    requires |prices| > 0
    decreases |prices|
    ensures Min(prices) in prices
    ensures forall p :: p in prices ==> Min(prices) <= p
{
    if |prices| == 1 then 
        prices[0]
    else 
        var restMin := Min(prices[1..]);
        if prices[0] <= restMin then (
            assert forall p :: p in prices[1..] ==> restMin <= p;
            assert forall p :: p in prices[1..] ==> prices[0] <= restMin <= p;
            assert forall p :: p in prices ==> (p == prices[0] || p in prices[1..]);
            prices[0]
        ) else (
            assert prices[0] > restMin;
            assert forall p :: p in prices[1..] ==> restMin <= p;
            assert restMin <= prices[0];
            assert forall p :: p in prices ==> (p == prices[0] || p in prices[1..]);
            assert forall p :: p in prices ==> restMin <= p;
            restMin
        )
}

method solve(n: int, v: int, sellers: seq<seq<int>>) returns (count: int, indices: seq<int>)
    requires ValidInput(n, v, sellers)
    ensures ValidOutput(count, indices, n)
    ensures CorrectSolution(v, sellers, indices)
{
    var ans := [];
    var i := 0;
    while i < n && i < |sellers|
        invariant 0 <= i <= n
        invariant i <= |sellers|
        invariant |ans| <= i
        invariant forall j :: 0 <= j < |ans| ==> 1 <= ans[j] <= i
        invariant forall j :: 0 <= j < |ans| - 1 ==> ans[j] < ans[j+1]
        invariant forall j :: 0 <= j < |ans| ==> v > Min(sellers[ans[j] - 1])
        invariant forall j :: 0 <= j < i ==> (v > Min(sellers[j]) <==> (j + 1) in ans)
    {
        if |sellers[i]| > 0 {
            var minPrice := Min(sellers[i]);
            if v > minPrice {
                ans := ans + [i + 1];
            }
        }
        i := i + 1;
    }

    return |ans|, ans;
}
