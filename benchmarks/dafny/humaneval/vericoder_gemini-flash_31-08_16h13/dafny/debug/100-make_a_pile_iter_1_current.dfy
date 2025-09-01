

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method make_a_pile(n: int) returns (pile: seq<int>)
  // pre-conditions-start
  requires n >= 0
  // pre-conditions-end
  // post-conditions-start
  ensures |pile| == n
  ensures forall i :: 1 <= i < n ==> pile[i] == pile[i - 1] + 2
  ensures n > 0 ==> pile[0] == n
  // post-conditions-end
// </vc-spec>
// <vc-code>
{
    var pile_array: array<int>;
    if n > 0 {
        pile_array := new int[n];
        pile_array[0] := n;
        var i := 1;
        while i < n
            invariant 1 <= i <= n
            invariant forall k :: 1 <= k < i ==> pile_array[k] == pile_array[k-1] + 2
            invariant forall k :: 0 <= k < i ==> pile_array[k] == n + 2 * k
        {
            pile_array[i] := pile_array[i-1] + 2;
            i := i + 1;
        }
    } else {
        pile_array := new int[0];
    }
    pile := pile_array[..];
}
// </vc-code>

