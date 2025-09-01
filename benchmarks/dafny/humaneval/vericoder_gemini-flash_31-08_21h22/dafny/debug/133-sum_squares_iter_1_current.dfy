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

lemma sum_squares_lemma(lst: seq<real>)
  ensures sum(square_seq(lst)) == sum_squares_helper(lst, 0)
{
  var n := |lst|;
  new_induction_lemma_sum_squares(lst, 0, n);
}

lemma new_induction_lemma_sum_squares(lst: seq<real>, k: int, n: int)
  requires 0 <= k <= n == |lst|
  ensures sum(square_seq(lst)[k..n]) == sum_squares_helper(lst, k)
  decreases n - k
{
  if k < n {
    calc {
      sum(square_seq(lst)[k..n]);
      square_seq(lst)[k] + sum(square_seq(lst)[k+1..n]);
      (ceil(lst[k]) * ceil(lst[k])) + sum_squares_helper(lst, k+1);
      sum_squares_helper(lst, k);
    }
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
  sum_squares_lemma(lst);
  return sum_squares_helper(lst, 0);
}
// </vc-code>

