// <vc-preamble>
function sum(s: seq<int>) : int
{
    if |s| == 0 then 0 else s[0] + sum(s[1..])
}
function square_seq(lst: seq<int>) : (sq : seq<int>)
    ensures |sq| == |lst|
{
    seq(|lst|, i requires 0 <= i < |lst| => if i % 3 == 0 then lst[i] * lst[i] else (if i % 4 == 0 then lst[i] * lst[i] * lst[i] else lst[i]))
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): implemented the proof for SumAppend via induction */
lemma SumAppend(s1: seq<int>, s2: seq<int>)
  decreases |s1|
  ensures sum(s1 + s2) == sum(s1) + sum(s2)
{
  if |s1| > 0 {
    SumAppend(s1[1..], s2);
  }
}
// </vc-helpers>

// <vc-spec>
method sum_squares(lst: seq<int>) returns (r : int)

    ensures r == sum(square_seq(lst))
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): re-verified, the logic is sound with the proven helper lemma */
{
  r := 0;
  var i := 0;
  var sq_lst := square_seq(lst);
  while i < |lst|
    invariant 0 <= i <= |lst|
    invariant r == sum(sq_lst[..i])
    invariant sq_lst == square_seq(lst)
    invariant |sq_lst| == |lst|
  {
    SumAppend(sq_lst[..i], [sq_lst[i]]);
    r := r + sq_lst[i];
    i := i + 1;
  }
}
// </vc-code>
