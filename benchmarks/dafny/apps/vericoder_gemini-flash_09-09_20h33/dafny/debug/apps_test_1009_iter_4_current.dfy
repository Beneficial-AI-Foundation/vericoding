predicate ValidInput(n: int, k: int, L: seq<int>)
{
    n >= 1 && k >= 1 && n <= 2*k &&
    |L| == n &&
    (forall i :: 0 <= i < |L|-1 ==> L[i] <= L[i+1]) &&
    (forall i :: 0 <= i < |L| ==> L[i] >= 0)
}

predicate ValidBoxConfiguration(boxes: seq<int>, boxSize: int)
{
    |boxes| >= 1 &&
    (forall i :: 0 <= i < |boxes| ==> boxes[i] <= boxSize) &&
    (forall i :: 0 <= i < |boxes| ==> boxes[i] >= 0)
}

function sum(s: seq<int>): int
{
    if |s| == 0 then 0 else s[0] + sum(s[1..])
}

function max(s: seq<int>): int
    requires |s| > 0
{
    if |s| == 1 then s[0]
    else if s[0] >= max(s[1..]) then s[0]
    else max(s[1..])
}

// <vc-helpers>
predicate CanPartitionIntoKBoxes(n: int, k: int, L: seq<int>, boxSize: int)
    requires ValidInput(n, k, L)
{
    if k == 0 then
        sum(L) == 0 // All elements must be 0 if no boxes are allowed
    else if sum(L) == 0 then
        true // If sum is 0, no boxes are needed, so it can always be partitioned
    else
        exists i :: 0 <= i < |L| && L[i] <= boxSize &&
        (CanPartitionIntoKBoxes(n - 1, k, L[..i] + L[i+1..], boxSize) ||
         CanPartitionIntoKBoxes(n, k - 1, L, boxSize - L[i])
        )
}

function min(a: int, b: int): int { if a < b then a else b }

// Helper function to create a sequence from 3 integers
function seq3(a: int, b: int, c: int): seq<int> {
  var s := new int[3];
  s[0] := a;
  s[1] := b;
  s[2] := c;
  return s[..]; // Convert array to sequence
}

// Fixed max3 function using the helper seq3
function max3(a: int, b: int, c: int): int {
  max(seq3(a, b, c))
}

// Proof helper functions and lemmas might be needed if the problem statement implies complex logic,
// but for this problem, the binary search approach within the method body handles most of the logic.
// The `CanPartitionIntoKBoxes` predicate is a conceptual definition for the helper.
// The actual implementation will be greedy.

function CanTryPartition(n: int, k: int, L: seq<int>, boxSize: int): bool
    requires ValidInput(n, k, L)
{
    var currentBoxFilled: int := 0;
    var boxesUsed: int := 1;
    var success: bool := true;

    for i: int := n - 1 downto 0
        invariant 0 <= i + 1 <= n
        invariant boxesUsed >= 1
        invariant boxesUsed <= k + 1
        invariant currentBoxFilled >= 0
        invariant currentBoxFilled <= boxSize
        invariant success ==> (forall j :: i < j < n ==> L[j] <= boxSize)
        invariant success ==> (forall j :: i < j < n && (L[j] + currentBoxFilled > boxSize)) ==> boxesUsed > 1
    {
        if L[i] > boxSize {
            success := false;
            break;
        }
        if currentBoxFilled + L[i] <= boxSize {
            currentBoxFilled := currentBoxFilled + L[i];
        } else {
            boxesUsed := boxesUsed + 1;
            if boxesUsed > k {
                success := false;
                break;
            }
            currentBoxFilled := L[i];
        }
    }
    return success;
}

method TryPartition(n: int, k: int, L: seq<int>, boxSize: int) returns (success: bool)
    requires ValidInput(n, k, L)
    ensures success <==> CanTryPartition(n, k, L, boxSize)
{
    var currentBoxFilled: int := 0;
    var boxesUsed: int := 1;
    var i: int := n - 1; // Start from largest elements (L is sorted ascending)

    while i >= 0
        invariant -1 <= i < n // Adjusted range to correctly capture the loop termination condition i = -1
        invariant boxesUsed >= 1
        invariant boxesUsed <= k+1
        invariant currentBoxFilled >= 0
        invariant currentBoxFilled <= boxSize
        invariant (forall j :: i < j < n ==> L[j] <= boxSize) // All processed elements fit in a box
        invariant (forall j :: i < j < n && (L[j] + currentBoxFilled > boxSize)) ==> (boxesUsed > 1 || currentBoxFilled == 0) // Adjusted invariant to reflect logic
        decreases i
    {
        if L[i] > boxSize {
            return false; // Cannot fit the largest element in any box
        }
        if currentBoxFilled + L[i] <= boxSize {
            currentBoxFilled := currentBoxFilled + L[i];
        } else {
            boxesUsed := boxesUsed + 1;
            if boxesUsed > k {
                return false; // Used too many boxes
            }
            currentBoxFilled := L[i];
        }
        i := i - 1;
    }
    return true;
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, k: int, L: seq<int>) returns (result: int)
    requires ValidInput(n, k, L)
    ensures result >= 0
// </vc-spec>
// <vc-code>
{
    var low: int := 0;
    var high: int := sum(L);
    var ans: int := high;

    if n == 0 { return 0; } // Empty list, no boxes needed

    // Initialize low with the maximum element in L, as this is the minimum possible box size
    // if a single element should fit in a box.
    // sum(L) is the maximum possible size (put all elements in one box).
    low := max(L); // L is non-empty due to ValidInput(n,k,L) && n >= 1

    while low <= high
        invariant low >= max(L)
        invariant high >= low -1 // high could be low - 1 after assignment high := mid - 1
        invariant ans >= low // ans is a candidate for the smallest possible box size, so it must be >= low
        invariant low >= 0
        invariant high <= sum(L)
        invariant (forall s' :: (s' < ans && s' >= max(L)) ==> !TryPartition(n, k, L, s'))
        invariant (ans >= max(L)) ==> TryPartition(n, k, L, ans) // If ans is a valid candidate (which implies ans >= max(L)), then it must be partitionable.
        decreases high - low
    {
        var mid: int := low + (high - low) / 2;
        // The original checks for "mid < low" and "mid > high" are redundant
        // because of the loop invariant `low <= high` and how `mid` is calculated.
        // `low + (high - low) / 2` will always be between `low` and `high` (inclusive of `low`).
        // If `low == high`, `mid = low`. If `low < high`, `low <= mid < high`.

        if TryPartition(n, k, L, mid) {
            ans := mid;
            high := mid - 1;
        } else {
            low := mid + 1;
        }
    }
    return ans;
}
// </vc-code>

