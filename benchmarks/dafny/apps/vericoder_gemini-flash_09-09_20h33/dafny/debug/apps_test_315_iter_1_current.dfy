function sum(s: seq<int>): int
{
    if |s| == 0 then 0 else s[0] + sum(s[1..])
}

predicate ValidInput(n: int, k: int, a: seq<int>)
{
    n >= 1 && |a| == n && k >= 0 && forall i :: 0 <= i < n ==> a[i] >= 0
}

predicate ValidOutput(a: seq<int>, finalSchedule: seq<int>, additionalWalks: int, k: int)
{
    |finalSchedule| == |a| &&
    additionalWalks >= 0 &&
    forall i :: 0 <= i < |a| ==> finalSchedule[i] >= a[i] &&
    forall i :: 0 <= i < |a| - 1 ==> finalSchedule[i] + finalSchedule[i + 1] >= k &&
    additionalWalks == sum(finalSchedule) - sum(a)
}

// <vc-helpers>
function min(a: int, b: int): int {
    if a < b then a else b
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, k: int, a: seq<int>) returns (additionalWalks: int, finalSchedule: seq<int>)
    requires ValidInput(n, k, a)
    ensures ValidOutput(a, finalSchedule, additionalWalks, k)
// </vc-spec>
// <vc-code>
{
    var currentSchedule: seq<int> := a;
    additionalWalks := 0;

    if n == 1 {
        finalSchedule := currentSchedule;
        return;
    }

    // Step 1: Ensure sum of adjacent elements is at least k, propagating from left to right
    for i := 0 to n - 2
        invariant 0 <= i < n - 1
        invariant |currentSchedule| == n
        invariant forall j :: 0 <= j <= i ==> currentSchedule[j] >= a[j]
        invariant forall j :: 0 <= j < i ==> currentSchedule[j] + currentSchedule[j+1] >= k
        invariant additionalWalks == sum(currentSchedule) - sum(a)
    {
        if currentSchedule[i] + currentSchedule[i+1] < k {
            var diff := k - (currentSchedule[i] + currentSchedule[i+1]);
            currentSchedule := currentSchedule[0..i+1] + [currentSchedule[i+1] + diff] + currentSchedule[i+2..];
            additionalWalks := additionalWalks + diff;
        }
    }

    // Step 2: Ensure sum of adjacent elements is at least k, propagating from right to left
    // This handles cases where the last element might need to be increased to satisfy the k constraint with its left neighbor
    // while ensuring previous adjustments are not violated.
    for i := n - 2 downto 0
        invariant -1 <= i < n - 1
        invariant |currentSchedule| == n
        invariant forall j | i < j < n - 1 :: currentSchedule[j] + currentSchedule[j+1] >= k
        invariant forall j | 0 <= j < i :: currentSchedule[j] + currentSchedule[j+1] >= k // from step 1
        invariant forall j :: 0 <= j < n ==> currentSchedule[j] >= a[j]
        invariant additionalWalks == sum(currentSchedule) - sum(a)
    {
        if currentSchedule[i] + currentSchedule[i+1] < k {
            // It's crucial that we only increase currentSchedule[i]
            // Any increase to currentSchedule[i+1] would violate the invariant for currentSchedule[i+1] + currentSchedule[i+2]
            var diff := k - (currentSchedule[i] + currentSchedule[i+1]);
            currentSchedule := currentSchedule[0..i] + [currentSchedule[i] + diff] + currentSchedule[i+1..];
            additionalWalks := additionalWalks + diff;
        }
    }

    finalSchedule := currentSchedule;
}
// </vc-code>

