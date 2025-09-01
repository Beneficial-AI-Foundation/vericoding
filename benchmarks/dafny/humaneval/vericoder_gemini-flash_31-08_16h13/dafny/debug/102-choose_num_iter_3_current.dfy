

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method choose_num(x : int, y : int) returns (num : int)
  // pre-conditions-start
  requires 0 <= x && 0 <= y
  // pre-conditions-end
  // post-conditions-start
  ensures num == -1 || (num >= x && num <= y)
  ensures num == -1 || num % 2 == 0
  ensures num == -1 || (forall i : int :: x <= i <= y && i % 2 == 0 ==> num >= i)
  ensures num == -1 <==> x >= y
  // post-conditions-end
// </vc-spec>
// <vc-code>
{
    if x >= y then
        return -1;
    else
        var current_max_even := -1;
        var i := x;
        while i <= y
            invariant x <= i <= y + 1
            invariant current_max_even == -1 || (current_max_even >= x && current_max_even <= y)
            invariant current_max_even == -1 || current_max_even % 2 == 0
            invariant current_max_even == -1 || (forall k : int :: (x <= k < i && k % 2 == 0) ==> current_max_even >= k)
            invariant current_max_even == -1 || (exists k :: current_max_even == k && k % 2 == 0 && x <= k < i) || (current_max_even == -1 && forall k :: (x <= k < i && k % 2 == 0) ==> false)
        {
            if i % 2 == 0 then
                current_max_even := i;
            i := i + 1;
        }
        return current_max_even;
}
// </vc-code>

