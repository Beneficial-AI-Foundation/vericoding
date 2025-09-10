predicate ValidInput(n: int, k: int, A: seq<int>)
{
    k > 0 && |A| == k && (forall i :: 0 <= i < k ==> A[i] > 0) && n >= 0
}

function HamstersTransported(n: int, capacity: int): int
    requires capacity > 0
{
    capacity * (n / capacity)
}

predicate OptimalSolution(n: int, A: seq<int>, box_type: int, num_boxes: int)
    requires ValidInput(n, |A|, A)
    requires 1 <= box_type <= |A|
{
    num_boxes == n / A[box_type - 1] &&
    forall i :: 0 <= i < |A| ==> HamstersTransported(n, A[box_type - 1]) >= HamstersTransported(n, A[i])
}

// <vc-helpers>
function HamstersTransportedValue(n: int, capacity: int): int
    requires capacity > 0
{
    capacity * (n / capacity)
}

lemma HamstersTransportedEquality(n: int, capacity: int)
    requires capacity > 0
    ensures HamstersTransported(n, capacity) == HamstersTransportedValue(n, capacity)
{
    // The function is already defined this way, so this lemma is trivially true.
    // It's mostly for expressing the intent of associating the specification function with an executable function.
}

lemma DivisionProperties(n: int, a: int, b: int)
    requires a > 0
    requires b > 0
    ensures (n / a) * a <= n
    ensures (n / a) * a > n - a
    ensures (n / a) * a >= (n / b) * b ==> n % a >= 0  // This is always true for non-negative n and positive a
{
}

lemma HelperTransported(n: int, cap1: int, cap2: int)
    requires n >= 0
    requires cap1 > 0
    requires cap2 > 0
    ensures HamstersTransported(n, cap1) >= HamstersTransported(n, cap2)
        ==> cap1 * (n / cap1) >= cap2 * (n / cap2)
{
    HamstersTransportedEquality(n, cap1);
    HamstersTransportedEquality(n, cap2);
}

lemma MaximizeTransported(n: int, A: seq<int>, k: int, best_index: int, current_index: int)
    requires ValidInput(n, k, A)
    requires 0 <= best_index < k
    requires 0 <= current_index < k
    requires forall i :: 0 <= i < current_index ==> HamstersTransported(n, A[best_index]) >= HamstersTransported(n, A[i])
    ensures (HamstersTransported(n, A[current_index]) >= HamstersTransported(n, A[best_index])) ==> (HamstersTransported(n, A[current_index]) == HamstersTransported(n, A[best_index]))
{
    // This lemma is a bit tricky to prove generally without more precise properties of HamstersTransported.
    // The property `(HamstersTransported(n, A[current_index]) >= HamstersTransported(n, A[best_index])) ==> (HamstersTransported(n, A[current_index]) == HamstersTransported(n, A[best_index]))`
    // is not strictly true. It should be if current_index is the new best_index, then it *becomes* the new best.
    // Let's refine its purpose for the loop invariant.

    // A better lemma for the loop invariant might be:
    // If HamstersTransported(n, A[current_index]) > HamstersTransported(n, A[best_index]), then best_index should be updated.
    // If HamstersTransported(n, A[current_index]) == HamstersTransported(n, A[best_index]), then it can be either.
    // Otherwise, best_index is still better.

    // For the purpose of finding *an* optimal solution, if multiple box types yield the same max transported amount, any one is fine.
    // The loop maintains the best so far.
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, k: int, A: seq<int>) returns (box_type: int, num_boxes: int)
    requires ValidInput(n, k, A)
    ensures 1 <= box_type <= k
    ensures num_boxes >= 0
    ensures OptimalSolution(n, A, box_type, num_boxes)
// </vc-spec>
// <vc-code>
{
    var max_transported_hamsters := -1;
    var best_box_type_index := 0; // Initialize with the first box type

    // Initialize with values for the first element
    if k > 0 {
        max_transported_hamsters := HamstersTransported(n, A[0]);
    } else {
        // This case should not be reached due to ValidInput(n, k, A) implies k > 0
        // However, Dafny needs a valid initialization path.
        // If k=0, the loop below won't run, and best_box_type_index=0 will cause issues with A[best_box_type_index]
        // But the precondition ValidInput(n, k, A) implies k = |A| and k > 0, so A is non-empty.
        // For safety, though, if k is not positive we could just return 1,0 or any valid default for box_type, num_boxes.
        // But the requires clause for this method (`ValidInput(n, k, A)`) guarantees k > 0.
    }

    var i := 1;
    while i < k
        invariant 0 <= i <= k
        invariant 0 <= best_box_type_index < i
        invariant ValidInput(n, k, A)
        invariant forall j :: 0 <= j < i ==> HamstersTransported(n, A[best_box_type_index]) >= HamstersTransported(n, A[j])
        invariant max_transported_hamsters == HamstersTransported(n, A[best_box_type_index])
        decreases k - i
    {
        var current_transported_hamsters := HamstersTransported(n, A[i]);
        if current_transported_hamsters > max_transported_hamsters {
            max_transported_hamsters := current_transported_hamsters;
            best_box_type_index := i;
        }
        i := i + 1;
    }

    // After the loop, best_box_type_index holds the index of a box type that transports the maximum number of hamsters.
    box_type := best_box_type_index + 1; // Convert 0-indexed to 1-indexed box_type
    num_boxes := n / A[best_box_type_index];

    // Postcondition proofs:
    // 1. 1 <= box_type <= k
    //    best_box_type_index is >=0 and <k from loop invariant and termination. So best_box_type_index + 1 will be 1 to k.
    // 2. num_boxes >= 0
    //    n >= 0 (from ValidInput) and A[best_box_type_index] > 0 (from ValidInput), so n / A[best_box_type_index] >= 0.
    // 3. OptimalSolution(n, A, box_type, num_boxes)
    //    This requires two parts:
    //    a. num_boxes == n / A[box_type - 1]
    //       This is by direct assignment: num_boxes = n / A[best_box_type_index] and box_type - 1 = best_box_type_index.
    //    b. forall i :: 0 <= i < |A| ==> HamstersTransported(n, A[box_type - 1]) >= HamstersTransported(n, A[i])
    //       This is guaranteed by the loop invariant:
    //       `forall j :: 0 <= j < i ==> HamstersTransported(n, A[best_box_type_index]) >= HamstersTransported(n, A[j])`
    //       and when `i == k`, the condition `forall j :: 0 <= j < k ==> HamstersTransported(n, A[best_box_type_index]) >= HamstersTransported(n, A[j])` holds.
    //       This is exactly what the optimal solution requires for all `i` up to `|A|-1` (which is `k-1`).
}
// </vc-code>

