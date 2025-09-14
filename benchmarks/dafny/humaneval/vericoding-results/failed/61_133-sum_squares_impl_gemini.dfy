// <vc-preamble>
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
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): added lemmas for sequence properties */
lemma sum_append(s: seq<int>, x: int)
  ensures sum(s + [x]) == sum(s) + x
  decreases |s|
{
  if |s| > 0 {
    sum_append(s[1..], x);
  }
}

lemma square_seq_append(s: seq<real>, y: real)
  ensures square_seq(s + [y]) == square_seq(s) + [ceil(y) * ceil(y)]
{
}
// </vc-helpers>

// <vc-spec>
method sum_squares(lst: seq<real>) returns (r : int)

    ensures r == sum(square_seq(lst))
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): call helper lemmas in loop to maintain invariant */
  r := 0;
  var i := 0;
  while i < |lst|
    invariant 0 <= i <= |lst|
    invariant r == sum(square_seq(lst[..i]))
  {
    var c := ceil(lst[i]);
    var sq_val := c * c;
    
    square_seq_append(lst[..i], lst[i]);
    sum_append(square_seq(lst[..i]), sq_val);

    r := r + sq_val;
    i := i + 1;
  }
}
// </vc-code>
