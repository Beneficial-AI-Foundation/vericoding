function sum(s: seq<int>) : int
    {
        if |s| == 0 then 0 else s[0] + sum(s[1..])
    }
function ceil(f: real) : (c : int)
    {
        (f + 1.0).Floor
    }
function square_seq(lst: seq<real>) : (sq : seq<int>)
        ensures |sq| == |lst|
    {
        seq(|lst|, i requires 0 <= i < |lst| => ceil(lst[i]) * ceil(lst[i]))
    }

// <vc-helpers>
function sum_of_squares_real(lst: seq<real>) : int
{
  if |lst| == 0 then 0
  else ceil(lst[0]) * ceil(lst[0]) + sum_of_squares_real(lst[1..])
}
// </vc-helpers>

// <vc-spec>
method sum_squares(lst: seq<real>) returns (r : int)
    // post-conditions-start
    ensures r == sum(square_seq(lst))
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    var r_int := 0;
    for i := 0 to |lst|
        invariant 0 <= i <= |lst|
        invariant r_int == sum(square_seq(lst[0..i]))
    {
        if i < |lst| {
            r_int := r_int + ceil(lst[i]) * ceil(lst[i]);
        }
    }
    return r_int;
}
// </vc-code>

