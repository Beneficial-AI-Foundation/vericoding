function sum(s: seq<int>) : int
{
    if |s| == 0 then 0 else s[0] + sum(s[1..])
}
function square_seq(lst: seq<int>) : (sq : seq<int>)
    ensures |sq| == |lst|
{
    seq(|lst|, i requires 0 <= i < |lst| => if i % 3 == 0 then lst[i] * lst[i] else (if i % 4 == 0 then lst[i] * lst[i] * lst[i] else lst[i]))
}

// <vc-helpers>
function total_sum(lst: seq<int>, k: int) : int
  requires 0 <= k <= |lst|
{
  if k == 0 then 0 else
    total_sum(lst, k-1) + 
      (if (k-1) % 3 == 0 then lst[k-1] * lst[k-1] else if (k-1) % 4 == 0 then lst[k-1] * lst[k-1] * lst[k-1] else lst[k-1])
}
// </vc-helpers>

// <vc-spec>
method sum_squares(lst: seq<int>) returns (r : int)
    // post-conditions-start
    ensures r == sum(square_seq(lst))
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
  r := 0;
  var i := 0;
  while i < |lst|
    invariant r == total_sum(lst, i)
  {
    var val := lst[i];
    if i % 3 == 0 {
      val := val * val;
    } else if i % 4 == 0 {
      val := val * val * val;
    }
    r := r + val;
    i := i + 1;
  }
}
// </vc-code>

