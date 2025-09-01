

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
        var numm := -1;
        var i := x;
        while i <= y
            invariant x <= i <= y + 1
            invariant numm == -1 || (numm >= x && numm <= i && numm % 2 == 0)
            invariant forall k : int :: x <= k < i && k % 2 == 0 ==> numm >= k
        {
            if i % 2 == 0 {
                if numm == -1 || i > numm {
                    numm := i;
                }
            }
            i := i + 1;
        }
        return numm;
}
// </vc-code>

