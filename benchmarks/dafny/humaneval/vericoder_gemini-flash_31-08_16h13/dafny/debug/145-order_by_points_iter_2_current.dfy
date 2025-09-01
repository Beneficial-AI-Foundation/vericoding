function digits_sum_pos(n: int): int
  requires n >= 0
{
  if n < 10 then n else digits_sum_pos(n / 10) + n % 10
}
function digits_sum(n: int): int {
  if n < 0 then digits_sum_pos(-n) else digits_sum_pos(n)
}

// <vc-helpers>
function get_points(value: int): int {
  return digits_sum(value);
}

predicate is_sorted_by_points(a: seq<int>) {
  forall i, j :: 0 <= i < j < |a| ==> get_points(a[i]) <= get_points(a[j])
}
// </vc-helpers>

// <vc-spec>
method order_by_points(s: seq<int>) returns (sorted: seq<int>)
  // post-conditions-start
  ensures forall i, j :: 0 <= i < j < |sorted| ==> digits_sum(sorted[i]) <= digits_sum(sorted[j])
  ensures |sorted| == |s|
  ensures multiset(s) == multiset(sorted)
  // post-conditions-end
// </vc-spec>
// <vc-code>
{
    var n := |s];
    if n == 0 {
        return [];
    }

    // Convert sequence to a mutable array for sorting
    var a := new int[n];
    for i := 0 to n - 1 {
        a[i] := s[i];
    }

    // Bubble sort variant
    for i := 0 to n - 2
        decreases n - i
        invariant 0 <= i <= n - 1
        invariant forall k, l :: 0 <= k < l < i ==> get_points(a[k]) <= get_points(a[l]) // elements from 0 to i-1 are sorted
        invariant forall k :: 0 <= k < i ==> (forall l :: i <= l < n ==> get_points(a[k]) <= get_points(a[l])) // elements from 0 to i-1 are smaller than or equal to elements from i to n-1
        invariant multiset(s) == multiset(a[0 .. n]) // invariant: elements in 'a' are a permutation of 's'
    {
        for j := n - 1 downto i + 1
            decreases j - i
            invariant i <= j <= n
            invariant forall k, l :: j <= k < l < n ==> get_points(a[k]) <= get_points(a[l]) // elements from j to n-1 are sorted relative to each other
            invariant multiset(s) == multiset(a[0 .. n]) // invariant: elements in 'a' are a permutation of 's'
        {
            if get_points(a[j]) < get_points(a[j-1]) {
                var temp := a[j];
                a[j] := a[j-1];
                a[j-1] := temp;
            }
        }
    }

    // Convert the sorted array back to a sequence
    sorted := a[0 .. n];
    
    // Prove postconditions
    assert is_sorted_by_points(sorted); // Proves the first ensures clause
    assert |sorted| == |s|; // Proves the second ensures clause
    assert multiset(s) == multiset(sorted); // Proves the third ensures clause
}
// </vc-code>

