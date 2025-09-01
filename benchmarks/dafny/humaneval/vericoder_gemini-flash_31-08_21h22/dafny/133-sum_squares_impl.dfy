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
function sum_squares_helper(lst: seq<real>, i: int) : int
  requires 0 <= i <= |lst|
  decreases |lst| - i
{
  if i == |lst| then
    0
  else
    ceil(lst[i]) * ceil(lst[i]) + sum_squares_helper(lst, i + 1)
}

lemma sum_squares_lemma_induction(lst: seq<real>, k: int)
  requires 0 <= k <= |lst|
  ensures sum(square_seq(lst)[k .. |lst|]) == sum_squares_helper(lst, k)
  decreases |lst| - k
{
  if k < |lst| {
    calc {
      sum(square_seq(lst)[k .. |lst|]);
      square_seq(lst)[k] + sum(square_seq(lst)[k + 1 .. |lst|]);
      {
        sum_squares_lemma_induction(lst, k + 1);
      }
      ceil(lst[k]) * ceil(lst[k]) + sum_squares_helper(lst, k + 1);
      sum_squares_helper(lst, k);
    }
  } else {
    assert k == |lst|;
    assert square_seq(lst)[k .. |lst|] == []; // Fixed: empty sequence syntax
    assert sum([]) == 0; // Fixed: empty sequence syntax
    assert sum(square_seq(lst)[k .. |lst|]) == 0;
    assert sum_squares_helper(lst, k) == 0;
  }
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
  sum_squares_lemma_induction(lst, 0);
  return sum_squares_helper(lst, 0);
}
// </vc-code>

