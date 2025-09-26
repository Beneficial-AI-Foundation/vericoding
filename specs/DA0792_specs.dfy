// <vc-preamble>
predicate ValidInput(n: int, fontSizes: seq<int>, costs: seq<int>)
{
    n >= 3 && |fontSizes| == n && |costs| == n &&
    (forall i :: 0 <= i < n ==> fontSizes[i] >= 1 && fontSizes[i] <= 1000000000) &&
    (forall i :: 0 <= i < n ==> costs[i] >= 1 && costs[i] <= 100000000)
}

predicate ValidTripleExists(fontSizes: seq<int>)
{
    exists i, j, k :: 0 <= i < j < k < |fontSizes| && fontSizes[i] < fontSizes[j] < fontSizes[k]
}

function MinTripleCost(n: int, fontSizes: seq<int>, costs: seq<int>): int
    requires ValidInput(n, fontSizes, costs)
    requires ValidTripleExists(fontSizes)
{
    var validTriples := set i, j, k | 0 <= i < j < k < n && fontSizes[i] < fontSizes[j] < fontSizes[k] :: costs[i] + costs[j] + costs[k];
    if validTriples == {} then 0 else 
    var minCost := 0;
    if exists cost :: cost in validTriples && (forall other :: other in validTriples ==> cost <= other) then
        var cost :| cost in validTriples && (forall other :: other in validTriples ==> cost <= other);
        cost
    else 0
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method solve(n: int, fontSizes: seq<int>, costs: seq<int>) returns (result: int)
    requires ValidInput(n, fontSizes, costs)
    ensures result == -1 <==> !ValidTripleExists(fontSizes)
    ensures result >= 0 ==> (exists i, j, k :: 0 <= i < j < k < n && fontSizes[i] < fontSizes[j] < fontSizes[k] && result == costs[i] + costs[j] + costs[k] && 
                            (forall i', j', k' :: 0 <= i' < j' < k' < n && fontSizes[i'] < fontSizes[j'] < fontSizes[k'] ==> costs[i'] + costs[j'] + costs[k'] >= result))
// </vc-spec>
// <vc-code>
{
    var ans := 2000000000; // Large value instead of infinity
    var found := false;

    for j := 1 to n-1 
        invariant 0 <= j <= n-1
        invariant !found ==> ans == 2000000000
        invariant found ==> ans < 2000000000
        invariant found ==> (exists i, jj, k :: 0 <= i < jj < k < n && fontSizes[i] < fontSizes[jj] < fontSizes[k] && ans == costs[i] + costs[jj] + costs[k])
        invariant found ==> (forall i, jj, k :: 0 <= i < jj < k < n && fontSizes[i] < fontSizes[jj] < fontSizes[k] && jj < j ==> costs[i] + costs[jj] + costs[k] >= ans)
        invariant forall i, jj, k :: 0 <= i < jj < k < n && jj < j && fontSizes[i] < fontSizes[jj] < fontSizes[k] ==> costs[i] + costs[jj] + costs[k] >= ans
    {
        var ll := 2000000000;
        var lr := 2000000000;

        for q := j+1 to n
            invariant j < q <= n
            invariant lr >= 2000000000 ==> (forall qq :: j < qq < q && fontSizes[j] < fontSizes[qq] ==> false)
            invariant lr < 2000000000 ==> (exists qq :: j < qq < q && fontSizes[j] < fontSizes[qq] && lr == costs[qq])
            invariant lr < 2000000000 ==> (forall qq :: j < qq < q && fontSizes[j] < fontSizes[qq] ==> costs[qq] >= lr)
        {
            if fontSizes[j] < fontSizes[q] {
                if costs[q] < lr {
                    lr := costs[q];
                }
            }
        }

        for q := 0 to j
            invariant 0 <= q <= j
            invariant ll >= 2000000000 ==> (forall qq :: 0 <= qq < q && fontSizes[qq] < fontSizes[j] ==> false)
            invariant ll < 2000000000 ==> (exists qq :: 0 <= qq < q && fontSizes[qq] < fontSizes[j] && ll == costs[qq])
            invariant ll < 2000000000 ==> (forall qq :: 0 <= qq < q && fontSizes[qq] < fontSizes[j] ==> costs[qq] >= ll)
        {
            if fontSizes[j] > fontSizes[q] {
                if costs[q] < ll {
                    ll := costs[q];
                }
            }
        }

        if ll != 2000000000 && lr != 2000000000 {
            var total := ll + lr + costs[j];
            if total < ans {
                ans := total;
                found := true;
            }
        }
    }

    if found {
        result := ans;
    } else {
        result := -1;
    }
}
// </vc-code>
