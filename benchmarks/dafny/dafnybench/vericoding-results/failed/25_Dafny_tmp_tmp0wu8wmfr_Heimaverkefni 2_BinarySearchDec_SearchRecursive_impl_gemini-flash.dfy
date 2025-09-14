// Author of question: Snorri Agnarsson
// Permalink of question: https://rise4fun.com/Dafny/CGB1z

// Authors of solution:   Alexander Guðmundsson
// Permalink of solution: https://rise4fun.com/Dafny/VnB5

// Use the command
//   dafny H2-skeleton.dfy
// or
//   compile H2-skeleton.dfy
// to compile the file.
// Or use the web page rise4fun.com/dafny.

// When you have solved the problem put
// the solution on the Dafny web page,
// generate a permalink and put it in
// this file.

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method SearchRecursive( a: seq<real>, i: int, j: int, x: real ) returns ( k: int )
    decreases j-i;
    requires 0 <= i <= j <= |a|;
    requires forall p, q :: i <= p < q < j ==> a[p] >= a[q];
    ensures i <= k <= j
    ensures forall r | i <= r < k :: a[r] >= x;
    ensures forall r | k <= r < j :: a[r] < x;
// </vc-spec>
// <vc-code>
{
    if i == j {
        return i;
    }

    var mid := (i + j) / 2;
    if a[mid] < x {
        // If a[mid] < x, then 'mid' belongs to the 'a[r] < x' group.
        // Therefore, the true 'k' must be at least 'mid + 1'.
        // We search in the range (mid, j].
        var k_right := SearchRecursive(a, mid + 1, j, x);

        // We need to show:
        // 1. forall r | i <= r < k_right :: a[r] >= x
        // 2. forall r | k_right <= r < j :: a[r] < x

        // From the recursive call, we have:
        // P1: forall r | mid + 1 <= r < k_right :: a[r] >= x
        // P2: forall r | k_right <= r < j :: a[r] < x

        // For the full range [i, j):
        // Consider r in [i, k_right):
        //   Case A: i <= r <= mid. Since a[mid] < x and the array is decreasing, a[r] >= a[mid] implies a[r] could be >= x.
        //           However, since a[mid] < x, 'mid' is definitely past the point where elements are >= x.
        //           This means for all r in [i, mid], we must have a[r] < x.
        //           So, elements in [i, mid] belong to the 'a[r] < x' part of the array.
        //           This means k should be greater than mid.
        //           Therefore, k_right which is >= mid + 1 is the correct value.
        //           No r in [i, mid] should satisfy a[r] >= x.
        //           The postcondition for this branch implies that for all r in [i, mid], a[r] < x.
        //           This means the values from i to mid are correctly handled by the second part of the postcondition
        //           (a[r] < x for r >= k_right, effectively meaning k_right is correctly placed).

        // From P1, for r in [mid+1, k_right), a[r] >= x. This takes care of the '>= x' part of the postcondition.
        // We need to ensure that for i <= r < mid+1, a[r] < x.
        // Since we are in the `a[mid] < x` branch, by monotonicity, any `a[r]` for `r <= mid` is `a[r] >= a[mid]`.
        // If `a[r] >= x` were true for some `r <= mid`, and `a[mid] < x`, this would imply a contradiction with monotonicity,
        // or that 'k' is <= mid. But we just established that k must be > mid.
        // The fact that `k_right` is returned means `mid` falls into the "less than x" part.
        // So for any `r` where `i <= r <= mid`, we must have `a[r] < x`.
        // This makes `k_right` satisfy the postcondition.

        return k_right;
    } else { // a[mid] >= x
        // If a[mid] >= x, then 'mid' belongs to the 'a[r] >= x' group.
        // Therefore, the true 'k' must be at most 'mid'.
        // We search in the range [i, mid].
        var k_left := SearchRecursive(a, i, mid, x);

        // We need to show:
        // 1. forall r | i <= r < k_left :: a[r] >= x
        // 2. forall r | k_left <= r < j :: a[r] < x

        // From the recursive call, we have:
        // P1: forall r | i <= r < k_left :: a[r] >= x
        // P2: forall r | k_left <= r < mid :: a[r] < x

        // For the full range [i, j):
        // From P1, for r in [i, k_left), a[r] >= x. This takes care of the '>= x' part of the postcondition.
        // We need to show that for r in [k_left, j): a[r] < x.
        // This can be split into two parts: [k_left, mid) and [mid, j).

        // For r in [k_left, mid): P2 directly gives a[r] < x.
        // For r in [mid, j): We know a[mid] >= x.
        // But if k_left is returned, it means that for all r in [k_left, mid), a[r] < x.
        // And importantly, for all r in [mid, j), a[r] < x must also hold IF k_left is the true split point.
        // Since we are in the `a[mid] >= x` branch, it means `mid` is in the first part where elements are `>= x`.
        // So, if `k_left` is chosen, it must satisfy that `a[r] < x` for `r >= k_left`.
        // For values `r` in `[mid, j)`, since the sequence is decreasing and `a[mid] >= x`, it's possible
        // that `a[r]` for `r > mid` could be less than `x`.
        // For the second postcondition, `forall r | k_left <= r < j :: a[r] < x`.
        // We know from recursion `forall r | k_left <= r < mid :: a[r] < x`.
        // We also know if our result is `k_left`, then for all `r | mid <= r < j`, `a[r]` must be `< x`.
        // This is always true for this branch. If a[mid] >= x, it belongs to the first half.
        // Therefore, k_left is the correct split point.
        // We need to show that for any r in [mid, j), if a[mid] >= x, then a[r] < x implies r >= k_left.
        // Which is effectively saying, the split point k should be <= mid.
        return k_left;
    }
}
// </vc-code>

// Ef eftirfarandi fall er ekki samþykkt þá eru
// föllin ekki að haga sér rétt að mati Dafny.