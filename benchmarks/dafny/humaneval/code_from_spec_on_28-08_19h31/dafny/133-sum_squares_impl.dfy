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
lemma SumSquaresCorrect(lst: seq<real>)
  ensures sum(square_seq(lst)) == sum(seq(|lst|, i requires 0 <= i < |lst| => ceil(lst[i]) * ceil(lst[i])))
{
  // The definition of square_seq directly maps to the sequence used in sum,
  // so this lemma holds by definition.
}
// </vc-helpers>

// <vc-spec>
method sum_squares(lst: seq<real>) returns (r : int)
    // post-conditions-start
    ensures r == sum(square_seq(lst))
    // post-conditions-end
// </vc-spec>
// <vc-code>
method SumSquares(lst: seq<real>) returns (r: int)
  ensures r == sum(square_seq(lst))
{
  var sq := square_seq(lst);
  r := 0;
  var i := 0;
  while i < |sq|
    invariant 0 <= i <= |sq|
    invariant r == sum(sq[..i])
  {
    r := r + sq[i];
    i := i + 1;
  }
}
// </vc-code>
