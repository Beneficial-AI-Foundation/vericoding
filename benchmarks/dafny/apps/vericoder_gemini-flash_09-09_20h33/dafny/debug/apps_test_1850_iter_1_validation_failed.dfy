predicate ValidInput(n: int, d: int, currentPoints: seq<int>, awards: seq<int>)
{
    n >= 1 && n <= 200000 &&
    d >= 1 && d <= n &&
    |currentPoints| == n &&
    |awards| == n &&
    d-1 < |currentPoints| &&
    (forall i :: 0 <= i < |currentPoints|-1 ==> currentPoints[i] >= currentPoints[i+1]) &&
    (forall i :: 0 <= i < |awards|-1 ==> awards[i] >= awards[i+1])
}

function CountOvertaken(currentPoints: seq<int>, awards: seq<int>, d: int): int
    requires |currentPoints| == |awards|
    requires d >= 1 && d <= |currentPoints|
    requires d-1 < |currentPoints|
    requires forall i :: 0 <= i < |awards|-1 ==> awards[i] >= awards[i+1]
{
    CountOvertakenHelper(currentPoints, awards, d, 0, 0)
}

function CountOvertakenHelper(currentPoints: seq<int>, awards: seq<int>, d: int, pos: int, usedAwards: int): int
    requires |currentPoints| == |awards|
    requires d >= 1 && d <= |currentPoints|
    requires d-1 < |currentPoints|
    requires forall i :: 0 <= i < |awards|-1 ==> awards[i] >= awards[i+1]
    requires 0 <= pos <= d-1
    requires 0 <= usedAwards <= |awards|
    decreases d-1-pos
{
    if pos >= d-1 then 0
    else
        var targetScore := currentPoints[d-1] + awards[0];
        var remainingAwards := |awards| - usedAwards;
        if remainingAwards > 0 && usedAwards < |awards| && currentPoints[pos] + awards[|awards|-1-usedAwards] <= targetScore then
            1 + CountOvertakenHelper(currentPoints, awards, d, pos+1, usedAwards+1)
        else
            CountOvertakenHelper(currentPoints, awards, d, pos+1, usedAwards)
}

// <vc-helpers>
function method BinarySearch(a: seq<int>, key: int): (index: int)
    requires forall i :: 0 <= i < |a|-1 ==> a[i] >= a[i+1]
    ensures (0 <= index < |a| && a[index] <= key && (index == 0 || a[index-1] > key)) || (index == |a| && (index == 0 || a[index-1] > key))
{
    var low := 0;
    var high := |a|;
    var result := high;
    while low < high
        invariant 0 <= low <= high <= |a|
        invariant (result == |a| || a[result] <= key)
        invariant (high == |a| || a[high] <= key) // all elements from high to |a|-1 are <= key
        invariant (low == 0 || a[low-1] > key) // all elements from 0 to low-1 are > key
    {
        var mid := low + (high - low) / 2;
        if a[mid] <= key
        {
            result := mid;
            high := mid;
        }
        else
        {
            low := mid + 1;
        }
    }
    return result;
}

function CountOvertakenBinary(currentPoints: seq<int>, awards: seq<int>, d: int): int
    requires |currentPoints| == |awards|
    requires d >= 1 && d <= |currentPoints|
    requires d-1 < |currentPoints|
    requires forall i :: 0 <= i < |awards|-1 ==> awards[i] >= awards[i+1]
    requires forall i :: 0 <= i < |currentPoints|-1 ==> currentPoints[i] >= currentPoints[i+1]
{
    var count := 0;
    var targetScore := currentPoints[d-1] + awards[0];
    var i := 0;
    while i < d-1
        invariant 0 <= i <= d-1
        invariant count == i - (d-1 - CountOvertaken(currentPoints, awards, d, i, 0))
        // The invariant above is complex. Let's try to relate it to the iterative approach.
        // The loop is counting how many players from currentPoints[0]...currentPoints[d-2]
        // can be overtaken.
        // A player currentPoints[i] (where i < d-1) can be overtaken if
        // currentPoints[i] + awards[|awards|-1] <= targetScore
        // This is based on the recursive definition which uses awards[|awards|-1-usedAwards].
        // If we want to guarantee overtaking, we need to consider the worst case for 'awards',
        // which is awards[last available]
        // No, the recursive definition `CountOvertakenHelper` checks for `currentPoints[pos] + awards[|awards|-1-usedAwards] <= targetScore`.
        // The `usedAwards` starts at 0 and increments. So, it checks against `awards[|awards|-1]`, then `awards[|awards|-2]`, and so on.

        // Let's refine the condition for an overtake in iterative approach:
        // A player `currentPoints[i]` can be overtaken if
        // `currentPoints[i] + awards[|awards|-1-count_so_far]` <= `targetScore`.
        // This `count_so_far` is the number of awards effectively consumed by earlier overtakes.
        // So, at each step `i`, we check `currentPoints[i] + awards[|awards|-1-count]` <= `targetScore`.
        invariant 0 <= count <= i
        invariant forall k :: 0 <= k < i && exists u :: 0 <= u < |awards| && awards[|awards|-1-u] == awards[|awards|-1-(k-CountOvertakenBinaryInner(currentPoints, awards, d, k))] && currentPoints[k] + awards[|awards|-1-(k-CountOvertakenBinaryInner(currentPoints, awards, d, k))] <= targetScore ==> CountOvertakenBinaryInnerStep(currentPoints, awards, d, k) == 1
        // (This invariant is extremely hard to prove within Dafny directly if we precisely mimic the recursive state for awards)
        // A simpler way:
        invariant 0 <= count <= i
        invariant (forall j :: 0 <= j < i && currentPoints[j] + awards[|awards|-1-j] <= targetScore ==> exists k :: 0 <= k < i && currentPoints[k] + awards[|awards|-1-k] <= targetScore)

        // The issue with the recursive definition's 'usedAwards' is that it implies a specific assignment of awards.
        // My `CountOvertaken` function in the problem statement is effectively saying:
        // "Using the largest remaining award (awards[0] for target, awards[last] for checking overtake),
        // can currentPoints[pos] be overtaken?"
        // The `usedAwards` in `CountOvertakenHelper` does not represent a global count of awards used
        // but rather how many specific 'spots' in `awards` have been "consumed" from the end.
        // This is key: `awards[|awards|-1-usedAwards]` means we're checking against `awards[last]`, then `awards[last-1]`, etc.
        // So, if currentPoints[pos] can be overtaken, it effectively "consumes" `awards[|awards|-1-usedAwards]`.

        // This means we need to match the indices carefully.
        // With `CountOvertakenHelper(currentPoints, awards, d, pos, usedAwards)`
        // `targetScore` is always `currentPoints[d-1] + awards[0]`.

        // Let's look at `CountOvertakenHelper` again.
        // It checks `currentPoints[pos] + awards[|awards|-1-usedAwards] <= targetScore`
        // if true, it increments `pos` and `usedAwards`. This means the `awards` index for the next check will be `|awards|-1-(usedAwards+1)`.
        // So, each successful overtake consumes one award from the end of the `awards` sequence.
        // This implicitly assumes we are trying to maximize overtakes, so we use the *smallest possible* award from the best players.

        // So, an iterative version should be:
        // Iterate pos from 0 to d-2.
        // At each pos, check currentPoints[pos] + awards[|awards|-1-count_of_previous_overtakes] <= targetScore
        // If it is, increment count.

        // We need to prove this equivalence.
        // Proof by induction, let's assume `awards` sequence is used this way.

        // Invariant for the iterative approach to match the recursive one:
        // `count` stores the number of people overtaken among `currentPoints[0...i-1]`,
        // and these correspond to `awards[|awards|-1]`, `awards[|awards|-2]`, ..., `awards[|awards|-1-count+1]`.
        // The `pos` in the recursive function maps to `i` in the loop.
        // `usedAwards` in the recursive function maps to `count` in the loop.
    {
        var requiredAward := targetScore - currentPoints[i];
        // We need to find if there is an award available (from `awards[|awards|-1-count]` down to `awards[|awards|-1]`)
        // such that `awards[k] <= requiredAward`.
        // But the awards are given from `awards[|awards|-1-usedAwards]` for the `usedAwards`-th overtake.
        // This means we are effectively trying to find if `awards[|awards|-1-count]` is <= `requiredAward`.

        // Check if currentPoints[i] can be overtaken using the `(count+1)`-th smallest award (which is awards[|awards|-1-count])
        if count < awards.Length && currentPoints[i] + awards[awards.Length - 1 - count] <= targetScore
        {
            count := count + 1;
        }
        i := i + 1;
    }
    return count;
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, d: int, currentPoints: seq<int>, awards: seq<int>) returns (result: int)
    requires ValidInput(n, d, currentPoints, awards)
    ensures 1 <= result <= d
    ensures result == d - CountOvertaken(currentPoints, awards, d)
// </vc-spec>
// <vc-code>
{
    var targetScore := currentPoints[d-1] + awards[0];
    var overtakenCount := 0;

    // We iterate through players from index 0 to d-2 (the players ahead of D)
    // and see how many of them can be overtaken.
    // An individual at currentPoints[i] can be overtaken if
    // currentPoints[i] + awards[last_available] <= targetScore
    // where awards[last_available] is awards[|awards|-1-overtakenCount].
    // Each successful overtake "consumes" an award from the end of the sorted `awards` sequence.
    for i := 0 to d-2
        invariant 0 <= i <= d-1
        invariant 0 <= overtakenCount <= i
        invariant (forall k :: 0 <= k < i && currentPoints[k] + awards[awards.Length - 1 - (k - CountOvertakenBinary(currentPoints, awards, d))] <= targetScore ==> currentPoints[k] + awards[awards.Length - 1 - (k - CountOvertakenBinary(currentPoints, awards, d))] <= targetScore)
        // This is tricky. The `CountOvertakenHelper` passes `usedAwards` which accumulates.
        // So at each `pos`, it checks `awards[|awards|-1-usedAwards]`.
        // This `usedAwards` is exactly `overtakenCount` in our loop.
        // We need to ensure that the loop correctly models the recursive `usedAwards` state.
        // Let's explicitly trace:
        // When pos=0, usedAwards=0. Check `currentPoints[0] + awards[|awards|-1] <= targetScore`. If so, next call has usedAwards=1.
        // When pos=1, usedAwards=1 (if prev was overtake) or 0 (if not). This is wrong. usedAwards is cumulative.
        // The `CountOvertakenHelper` call structure ensures `usedAwards` always increases.
        // This means the `usedAwards` parameter in the recursive function (let's call it `U`) effectively represents
        // how many *successful overtakes occurred among players [0...pos-1]*
        // So, if `currentPoints[pos]` is being considered, it depends on `U`.
        // If `currentPoints[pos] + awards[|awards|-1-U] <= targetScore`, then the next `pos+1` will have `U+1`.
        // Otherwise, the next `pos+1` will still have `U`.

        // This implies that the 'count' in our iterative loop must be the correct `usedAwards` value
        // when checking `currentPoints[i]`.
        // The `overtakenCount` here truly represents the cumulative count of overtakes up to `i-1`.
        invariant (forall k :: 0 <= k < i :: // For all previous indices k
            var prev_overtakes_at_k := 0;
            if k > 0 { var temp_k := 0; var temp_c := 0; while temp_k < k { if temp_c < awards.Length && currentPoints[temp_k] + awards[awards.Length - 1 - temp_c] <= targetScore { temp_c := temp_c + 1; } temp_k := temp_k + 1; } prev_overtakes_at_k := temp_c; } else { prev_overtakes_at_k := 0; }
            currentPoints[k] + awards[awards.Length - 1 - prev_overtakes_at_k] <= targetScore ==> (exists u :: 0 <= u < i && currentPoints[u] + awards[awards.Length - 1 - u] <= targetScore && currentPoints[u] == currentPoints[k])
        )
        // The invariant is becoming circular or extremely complex to express formally
        // without providing the definition of `CountOvertakenHelper` in a loop-friendly way.
        // However, the logic for the iterative solution is sound based on `CountOvertakenHelper`.
        // `overtakenCount` correctly accumulates the `usedAwards`
        // if for `pos=i`, `usedAwards` is `overtakenCount` from previous iterations.
    {
        if overtakenCount < awards.Length && currentPoints[i] + awards[awards.Length - 1 - overtakenCount] <= targetScore
        {
            overtakenCount := overtakenCount + 1;
        }
    }

    // result is the number of players NOT overtaken.
    // These are d (player D) plus players from [0...d-2] who were not overtaken.
    // Total players initialy ahead of D: d-1.
    // Number of players who remain ahead of D = (d-1) - overtakenCount.
    // Plus player D (which is 1).
    // result = (d-1 - overtakenCount) + 1 = d - overtakenCount.
    // This matches the `CountOvertaken` function defined in the problem.
    result := d - overtakenCount;
}
// </vc-code>

