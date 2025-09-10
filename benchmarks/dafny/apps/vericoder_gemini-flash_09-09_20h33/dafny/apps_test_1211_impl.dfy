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

lemma HamstersTransportedIsMaximize(n: int, A: seq<int>, k: int, best_index: int)
    // Add preconditions that reflect the state when the lemma is called
    requires 0 <= best_index < k
    requires k == |A|
    requires (forall i :: 0 <= i < k ==> A[i] > 0)
    requires n >= 0
    // Add the specific invariant which holds from the loop and allows to prove the postcondition
    requires (forall j :: 0 <= j < k ==> HamstersTransported(n, A[best_index]) >= HamstersTransported(n, A[j]))
    ensures forall i :: 0 <= i < k ==> HamstersTransported(n, A[best_index]) >= HamstersTransported(n, A[i])
{}
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
    var max_transported_hamsters := HamstersTransported(n, A[0]);
    var best_box_type_index := 0; // Initialize with the first box type

    var i := 1;
    while i < k
        invariant 0 < k
        invariant 0 <= i <= k
        invariant 0 <= best_box_type_index < i || (i == 1 && best_box_type_index == 0) // if i=1, best_box_type_index must be 0
        invariant HamstersTransported(n, A[best_box_type_index]) == max_transported_hamsters
        invariant forall j :: 0 <= j < i ==> HamstersTransported(n, A[best_box_type_index]) >= HamstersTransported(n, A[j])
        decreases k - i
    {
        var current_transported_hamsters := HamstersTransported(n, A[i]);
        if current_transported_hamsters > max_transported_hamsters {
            max_transported_hamsters := current_transported_hamsters;
            best_box_type_index := i;
        }
        i := i + 1;
    }

    // The loop invariant 'forall j :: 0 <= j < i ==> HamstersTransported(n, A[best_box_type_index]) >= HamstersTransported(n, A[j])'
    // becomes 'forall j :: 0 <= j < k ==> HamstersTransported(n, A[best_box_type_index]) >= HamstersTransported(n, A[j])' at loop exit
    // due to i == k. This directly satisfies the precondition of HamstersTransportedIsMaximize.
    HamstersTransportedIsMaximize(n, A, k, best_box_type_index);
    box_type := best_box_type_index + 1;
    num_boxes := n / A[best_box_type_index];
}
// </vc-code>

